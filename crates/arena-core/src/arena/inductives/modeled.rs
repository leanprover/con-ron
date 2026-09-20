//! `arena::inductives::modeled` — the modeled-inductive install.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/Modeled.lean`, which is
//! `ConLeche/Kernel/Inductives/Modeled.lean` whole over handles: the member
//! checks against the `_model` artifacts under the group-local renaming, the
//! iota-rule checks against the `_model.iota_j` theorems, the capability
//! checks and the projection-function installs.
//!
//! ## The twin's deviations, and what they became
//!
//! * **`env` is `fe : IFEnv`**, so `env'`/`envSelf` are `fe2`/`fe_self` and
//!   the `…F` twins of `ConLeche/Kernel/DeclCheck.lean` collapse into these.
//! * **The renaming maps are TABLES.**  con-leche's `f : Name → Name` builds a
//!   name by `n.str "_model"`; over handles building a name means INTERNING
//!   one, so a pure `NIdx → NIdx` cannot do it.  Each map is precomputed as an
//!   association list — finitely many entries, all interned once — and
//!   `rename_by` is its lookup.  `RenameBy` is that list packaged as the
//!   `arena::expr_ops::NIdxToNIdx` dictionary `rename_consts_fast` takes, which
//!   is the twin's `renameBy tbl` partial application with the closure
//!   defunctionalised (DESIGN.md §3.4).  This is the last of con-leche's
//!   higher-order arguments and it is now data on both sides.
//! * **The three `foldlM`s are explicit recursions** (`check_ind_members`,
//!   `install_ind_recs`, `install_proj_fns`).
//! * **`eq_app3` spells con-leche's nested `Expr` pattern once**:
//!   `.app (.app (.app (.const c [ℓ]) ty) l) r` is four `view`s over handles
//!   and three of this module's checks match it.
//!
//! ## Two shapes the port adds
//!
//! * **the splits.**  `checkIotaThm` and `checkIotaThmN` are one `do` block of
//!   eighty lines each in the twin; here they are five functions each, split at
//!   the twin's own `let`-boundaries, which is task #97-P4c's arrangement and
//!   `con_ron_core::kernel::inductives::modeled`'s.
//! * **the messages are `con_ron_core`'s own**, interpolation dropped
//!   (task #97-P4c's row).  Where the twin distinguishes two messages that
//!   con-ron-core merges into one — the iota statement's head, arity and
//!   prefix pins — the port uses con-ron-core's merged constant, because what
//!   the message has to match is the differential's partner, not the twin's
//!   `s!` string (§3.1: a message need not match a theorem).

use super::ind_base;
use super::struct_parts;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IIndCaps, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::expr_ops::NIdxToNIdx;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::monad::{fail, intern_e, intern_n_node, read_name, view, view_ls, AState};
use crate::arena::store::{ENodeView, NNodeView};
use con_ron_core::kernel::basis_names;
use con_ron_core::kernel::core_k;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, code_points_from, CheckError};
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::expr::BinderMeta;
use con_ron_core::kernel::expr_ops::sub_nat;
use con_ron_core::kernel::level;
use con_ron_core::ron::hashmap::{Dup, Eq2};

// ---------------------------------------------------------------------------
// The messages (con-ron-core's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota statement lhs typ`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_LHS: [u32; 22] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 108, 104, 115, 32, 116,
    121, 112,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota statement rhs typ`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_RHS: [u32; 22] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 114, 104, 115, 32, 116,
    121, 112,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota type slot sort mismatc`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_SLOT: [u32; 27] = [
    105, 111, 116, 97, 32, 116, 121, 112, 101, 32, 115, 108, 111, 116, 32, 115, 111, 114, 116, 32,
    109, 105, 115, 109, 97, 116, 99,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `missing iota theorem for `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_MISS: [u32; 25] = [
    109, 105, 115, 115, 105, 110, 103, 32, 105, 111, 116, 97, 32, 116, 104, 101, 111, 114, 101,
    109, 32, 102, 111, 114, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota theorem level mismatch`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_LPS: [u32; 27] = [
    105, 111, 116, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 108, 101, 118, 101, 108, 32, 109,
    105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota statement shape mismatch `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_SHAPE: [u32; 30] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 115, 104, 97, 112, 101,
    32, 109, 105, 115, 109, 97, 116, 99, 104, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota statement not an eqn   `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_NOT_EQ: [u32; 28] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 110, 111, 116, 32, 97,
    110, 32, 101, 113, 110, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota statement head mismatch`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_HEAD: [u32; 28] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 104, 101, 97, 100, 32,
    109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota statement major mismatch`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_MAJ: [u32; 29] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 109, 97, 106, 111, 114,
    32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota constructor telescope`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_CTELE: [u32; 26] = [
    105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 101, 108,
    101, 115, 99, 111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota constructor indice`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_CIDX: [u32; 23] = [
    105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 105, 110, 100,
    105, 99, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota recursor telescope`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_RTELE: [u32; 23] = [
    105, 111, 116, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 116, 101, 108, 101, 115, 99,
    111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `rule shape mismatch`, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_RULE: [u32; 19] = [
    114, 117, 108, 101, 32, 115, 104, 97, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota statement mismatch `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_MIS: [u32; 24] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 109, 105, 115, 109, 97,
    116, 99, 104, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota constructor residual head `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_RHEAD: [u32; 31] = [
    105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 115,
    105, 100, 117, 97, 108, 32, 104, 101, 97, 100, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota constructor arity `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_IOTA_CARITY: [u32; 23] = [
    105, 111, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 97, 114, 105,
    116, 121, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `iota rule constructor     `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_RULE_CTOR: [u32; 26] = [
    105, 111, 116, 97, 32, 114, 117, 108, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
    114, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `rule field count mismatch `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_RULE_NF: [u32; 26] = [
    114, 117, 108, 101, 32, 102, 105, 101, 108, 100, 32, 99, 111, 117, 110, 116, 32, 109, 105, 115,
    109, 97, 116, 99, 104, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `loose bound variable in rule `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_RULE_BVAR: [u32; 29] = [
    108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101,
    32, 105, 110, 32, 114, 117, 108, 101, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `free variable in rule     `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_RULE_FVAR: [u32; 26] = [
    102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 114, 117, 108,
    101, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `undeclared universe parameter    `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_RULE_LPS: [u32; 33] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
    112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `model-shaped member name   `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_MODEL_NAME: [u32; 27] = [
    109, 111, 100, 101, 108, 45, 115, 104, 97, 112, 101, 100, 32, 109, 101, 109, 98, 101, 114, 32,
    110, 97, 109, 101, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `no install route for inductive block           `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_NO_ROUTE: [u32; 47] = [
    110, 111, 32, 105, 110, 115, 116, 97, 108, 108, 32, 114, 111, 117, 116, 101, 32, 102, 111, 114,
    32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 32, 32, 32, 32,
    32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `model level parameters mismatch       `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_MODEL_LPS: [u32; 38] = [
    109, 111, 100, 101, 108, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114, 97, 109, 101, 116, 101,
    114, 115, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `model type mismatch       `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_MODEL_TY: [u32; 26] = [
    109, 111, 100, 101, 108, 32, 116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32,
    32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `non-inductive member in block `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_NONIND: [u32; 30] = [
    110, 111, 110, 45, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 109, 101, 109, 98, 101, 114,
    32, 105, 110, 32, 98, 108, 111, 99, 107, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `recursor before other block members     `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_ORDER: [u32; 40] = [
    114, 101, 99, 117, 114, 115, 111, 114, 32, 98, 101, 102, 111, 114, 101, 32, 111, 116, 104, 101,
    114, 32, 98, 108, 111, 99, 107, 32, 109, 101, 109, 98, 101, 114, 115, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `modeled recursor requires the Eq basis      `, as code points — `con_ron_core::kernel::inductives::inductives_c`'s own, so the differential test can compare error text.
pub const M_EQ_BASIS: [u32; 44] = [
    109, 111, 100, 101, 108, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 114, 101,
    113, 117, 105, 114, 101, 115, 32, 116, 104, 101, 32, 69, 113, 32, 98, 97, 115, 105, 115, 32,
    32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection constructor not stored `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PL_CTOR: [u32; 34] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection constructor arity mismatch  `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PL_ARITY: [u32; 39] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 97, 114, 105, 116, 121, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `missing projection model  `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PL_MODEL: [u32; 26] = [
    109, 105, 115, 115, 105, 110, 103, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32,
    109, 111, 100, 101, 108, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection model level mismatch  `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PL_MLPS: [u32; 33] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 109, 111, 100, 101, 108, 32, 108, 101,
    118, 101, 108, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection name taken `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PL_TAKEN: [u32; 22] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 116, 97, 107, 101,
    110, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection parent not stored `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PL_PARENT: [u32; 29] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 112, 97, 114, 101, 110, 116, 32, 110, 111,
    116, 32, 115, 116, 111, 114, 101, 100, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota requires the pinned Eq     `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PL_EQ: [u32; 43] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 114, 101, 113, 117,
    105, 114, 101, 115, 32, 116, 104, 101, 32, 112, 105, 110, 110, 101, 100, 32, 69, 113, 32, 32,
    32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection type roundtrip    `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PT_ROUND: [u32; 29] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 114, 111, 117,
    110, 100, 116, 114, 105, 112, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection type resolution    `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PT_RES: [u32; 30] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 114, 101, 115,
    111, 108, 117, 116, 105, 111, 110, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection type wellformedness     `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PT_WF: [u32; 35] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 119, 101, 108,
    108, 102, 111, 114, 109, 101, 100, 110, 101, 115, 115, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection type telescope    `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PT_TELE: [u32; 29] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116, 101, 108,
    101, 115, 99, 111, 112, 101, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `missing projection iota theorem `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_MISS: [u32; 32] = [
    109, 105, 115, 115, 105, 110, 103, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32,
    105, 111, 116, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota level mismatch  `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_LPS: [u32; 32] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 108, 101, 118, 101,
    108, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota telescope    `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_TELE: [u32; 29] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 116, 101, 108, 101,
    115, 99, 111, 112, 101, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection constructor telescope    `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_CTELE: [u32; 36] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota domain mismatch  `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_DOM: [u32; 33] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 100, 111, 109, 97,
    105, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota head `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_HEAD: [u32; 21] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 104, 101, 97, 100,
    32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota redex mismatch `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_REDEX: [u32; 31] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 114, 101, 100, 101,
    120, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota field mismatch `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_FIELD: [u32; 31] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 102, 105, 101, 108,
    100, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection iota body shape  `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PI_SHAPE: [u32; 28] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 111, 116, 97, 32, 98, 111, 100, 121,
    32, 115, 104, 97, 112, 101, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection index out of range    `, as code points — `con_ron_core::kernel::inductives::modeled`'s own, so the differential test can compare error text.
pub const M_PROJ_RANGE: [u32; 33] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 110, 100, 101, 120, 32, 111, 117,
    116, 32, 111, 102, 32, 114, 97, 110, 103, 101, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection name family taken`, as code points — `con_ron_core::kernel::inductives::struct_install`'s own, so the differential test can compare error text.
pub const M_FAM_TAKEN: [u32; 28] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 102, 97, 109, 105,
    108, 121, 32, 116, 97, 107, 101, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `recursor before other block members     `, as code points — `con_ron_core::kernel::inductives::inductives_c`'s own, so the differential test can compare error text.
pub const M_ORDER_BLOCK: [u32; 40] = [
    114, 101, 99, 117, 114, 115, 111, 114, 32, 98, 101, 102, 111, 114, 101, 32, 111, 116, 104, 101,
    114, 32, 98, 108, 111, 99, 107, 32, 109, 101, 109, 98, 101, 114, 115, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `modeled structure: eta constructor residual    `, as code points — `con_ron_core::kernel::inductives::inductives_c`'s own, so the differential test can compare error text.
pub const M_ETA_RESID: [u32; 47] = [
    109, 111, 100, 101, 108, 101, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32, 101,
    116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 115, 105, 100,
    117, 97, 108, 32, 32, 32, 32,
];

// ---------------------------------------------------------------------------
// Two helpers of the modeled route (`Modeled.lean:40-71` of the twin)
//
// `arena::inductives::ind_base` carries the declaration checker's own twins;
// these two are the modeled install's, and the Lean twin deliberately leaves
// them here — the renaming domain comparison because renaming a constant over
// handles is monadic, and the `Eq`-basis guard because it is the one predicate
// three clauses of this file share and nothing else reads.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:56-65 domsMatchRenamed`
/// — `domsMatchAux` with the right side renamed (`g = fun _ e => e.renameConsts
/// f`, `checkProjIota`'s instance of con-leche's higher-order argument).  `f`
/// is the `NIdxToNIdx` dictionary `arena::expr_ops` already uses for
/// con-leche's one surviving function argument.
pub fn doms_match_renamed<F>(
    st: &mut AState,
    f: &F,
    bs1: &Vec<(EIdx, BinderMeta)>,
    bs2: &Vec<(EIdx, BinderMeta)>,
    o1: u64,
    o2: u64,
    k: u64,
) -> Result<bool, CheckError>
where
    F: NIdxToNIdx,
{
    if k == 0 {
        Ok(true)
    } else {
        let j1: u64 = o1 + k - 1;
        let j2: u64 = o2 + k - 1;
        if j1 >= bs1.len() as u64 || j2 >= bs2.len() as u64 {
            Ok(false)
        } else {
            let b2: EIdx = bs2[j2 as usize].0.dup2();
            match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, &b2) {
                Err(e) => Err(e),
                Ok(r) => {
                    if bs1[j1 as usize].0.eq2(&r) {
                        doms_match_renamed(st, f, bs1, bs2, o1, o2, k - 1)
                    } else {
                        Ok(false)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:71-74 eqBasisStored`
/// — `env.find? eqName = some eqA`, the "requires the pinned `Eq` basis"
/// guard, factored out because three call sites make it.  `eq_basis_ci` is the
/// comparand: the same `ConstantInfo` through the same store, hence the same
/// handle (`denoteE`/`denoteN` are injective, task #97a).
pub fn eq_basis_stored(st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match core::pin(st, &basis_names::eq_name()) {
        Err(e) => Err(e),
        Ok(en) => {
            let found: Option<IConstantInfo> = match env::ifenv_find(fe, &en) {
                Some(ci) => Some(env::i_constant_info_dup(ci)),
                None => None,
            };
            match found {
                Some(ci) => match ind_base::eq_basis_ci(st) {
                    Err(e) => Err(e),
                    Ok(want) => Ok(ind_base::i_constant_info_beq(&ci, &want)),
                },
                None => Ok(false),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The renaming tables (`Modeled.lean:44-87` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — look a name up in a precomputed rename table
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:48-51 renameBy` — a
/// name the table does not mention is its own image.
pub fn rename_by(tbl: &Vec<(NIdx, NIdx)>, n: &NIdx) -> NIdx {
    rename_by_from(tbl, 0, n)
}

/// con-leche: none — look a name up in a precomputed rename table
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:49 renameBy` — the
/// cursor recursion behind `rename_by` (`tbl.find? (·.1 == n)`).
pub fn rename_by_from(tbl: &Vec<(NIdx, NIdx)>, i: usize, n: &NIdx) -> NIdx {
    if i >= tbl.len() {
        n.dup2()
    } else if tbl[i].0.eq2(n) {
        tbl[i].1.dup2()
    } else {
        rename_by_from(tbl, i + 1, n)
    }
}

/// con-leche: none — replaces the `f : NIdx → NIdx` argument of `renameConsts`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:48-51 renameBy` —
/// the rename table packaged as the `NIdxToNIdx` dictionary
/// `arena::expr_ops::rename_consts_fast` takes.  It IS the twin's partial
/// application `renameBy tbl`, with the closure defunctionalised (§3.4).
pub struct RenameBy {
    pub tbl: Vec<(NIdx, NIdx)>,
}

/// con-leche: none — replaces the `f : NIdx → NIdx` argument of `renameConsts`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:48-51 renameBy`.
impl NIdxToNIdx for RenameBy {
    /// con-leche: none — the `f` of `renameConsts f`
    fn rename(&self, n: &NIdx) -> NIdx {
        rename_by(&self.tbl, n)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:56-61 blockRenameTable`
/// — the block renaming as a table: every member name maps to its `_model`
/// companion, every other name to itself.
pub fn block_rename_table(
    st: &mut AState,
    block_names: &Vec<NIdx>,
) -> Result<RenameBy, CheckError> {
    match block_rename_table_from(st, block_names, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(tbl) => Ok(RenameBy { tbl }),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:56-61 blockRenameTable`
/// — the cursor recursion behind `block_rename_table`.
pub fn block_rename_table_from(
    st: &mut AState,
    block_names: &Vec<NIdx>,
    i: usize,
    out: Vec<(NIdx, NIdx)>,
) -> Result<Vec<(NIdx, NIdx)>, CheckError> {
    if i >= block_names.len() {
        Ok(out)
    } else {
        let n: NIdx = block_names[i].dup2();
        match ind_base::model_name(st, &n) {
            Err(e) => Err(e),
            Ok(m) => {
                let mut o: Vec<(NIdx, NIdx)> = out;
                o.push((n, m));
                block_rename_table_from(st, block_names, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:65-74 projBack` —
/// rename a model-side projection type back to public names, as a table.
pub fn proj_back(st: &mut AState, t: &NIdx, ctor: &NIdx, n_f: u64) -> Result<RenameBy, CheckError> {
    match ind_base::model_name(st, t) {
        Err(e) => Err(e),
        Ok(tm) => match ind_base::model_name(st, ctor) {
            Err(e) => Err(e),
            Ok(cm) => {
                let mut out: Vec<(NIdx, NIdx)> = Vec::new();
                out.push((tm, t.dup2()));
                out.push((cm, ctor.dup2()));
                match proj_pairs_from(st, t, n_f, 0, true, out) {
                    Err(e) => Err(e),
                    Ok(tbl) => Ok(RenameBy { tbl }),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:78-87 projFwd` — the
/// forward (public → model) map on the projection family, as a table.
pub fn proj_fwd(st: &mut AState, t: &NIdx, ctor: &NIdx, n_f: u64) -> Result<RenameBy, CheckError> {
    match ind_base::model_name(st, t) {
        Err(e) => Err(e),
        Ok(tm) => match ind_base::model_name(st, ctor) {
            Err(e) => Err(e),
            Ok(cm) => {
                let mut out: Vec<(NIdx, NIdx)> = Vec::new();
                out.push((t.dup2(), tm));
                out.push((ctor.dup2(), cm));
                match proj_pairs_from(st, t, n_f, 0, false, out) {
                    Err(e) => Err(e),
                    Ok(tbl) => Ok(RenameBy { tbl }),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:457-464 projBack
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:466-473 projFwd
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:68-73 projBack.go`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:81-86 projFwd.go` —
/// the projection family's `nF` pairs, in one cursor recursion for both
/// directions (`back` swaps the two sides).  The twin writes the two `go`s
/// out; they differ only in that swap, and both intern the same two names in
/// the same order, so a shared body leaves the same store state.
pub fn proj_pairs_from(
    st: &mut AState,
    t: &NIdx,
    n_f: u64,
    j: u64,
    back: bool,
    out: Vec<(NIdx, NIdx)>,
) -> Result<Vec<(NIdx, NIdx)>, CheckError> {
    if j >= n_f {
        Ok(out)
    } else if back {
        match core::proj_model_name(st, t, j) {
            Err(e) => Err(e),
            Ok(a) => match env::proj_fn_name(&mut st.store, t, j) {
                Err(e) => Err(e),
                Ok(b) => {
                    let mut o: Vec<(NIdx, NIdx)> = out;
                    o.push((a, b));
                    proj_pairs_from(st, t, n_f, j + 1, back, o)
                }
            },
        }
    } else {
        match env::proj_fn_name(&mut st.store, t, j) {
            Err(e) => Err(e),
            Ok(a) => match core::proj_model_name(st, t, j) {
                Err(e) => Err(e),
                Ok(b) => {
                    let mut o: Vec<(NIdx, NIdx)> = out;
                    o.push((a, b));
                    proj_pairs_from(st, t, n_f, j + 1, back, o)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The equation pattern (`Modeled.lean:89-109` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — con-leche's `.app (.app (.app (.const c [ℓ]) ty) l) r`, read once
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:94-109 eqApp3?` —
/// the shape of every pinned iota/eta/unit statement body: the head's name, its
/// single level, the type slot and the two sides.
pub fn eq_app3(
    st: &AState,
    h: &EIdx,
) -> Result<Option<(NIdx, LIdx, EIdx, EIdx, EIdx)>, CheckError> {
    match view(st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::App(f1, r)) => match view(st, &f1) {
            Err(e) => Err(e),
            Ok(ENodeView::App(f2, l)) => match view(st, &f2) {
                Err(e) => Err(e),
                Ok(ENodeView::App(f3, ty)) => match view(st, &f3) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(c, us)) => match view_ls(st, &us) {
                        Err(e) => Err(e),
                        Ok(ls) => {
                            if ls.len() == 1 {
                                Ok(Some((c, ls[0].dup2(), ty, l, r)))
                            } else {
                                Ok(None)
                            }
                        }
                    },
                    Ok(_) => Ok(None),
                },
                Ok(_) => Ok(None),
            },
            Ok(_) => Ok(None),
        },
        Ok(_) => Ok(None),
    }
}

// ---------------------------------------------------------------------------
// The iota certificates (`Modeled.lean:111-226` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:31-53 checkIotaSidesTy
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:117-134 checkIotaSidesTy`
/// — certify that both sides of a modeled iota equation inhabit the equation's
/// type, and that the equation's type slot itself inhabits the sort the
/// statement's own `Eq.{ℓA}` names.  The slot certification is the TT lane's
/// (con-leche's task #147) and is skipped unless `mode.ttChecks`.
pub fn check_iota_sides_ty(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    depth: u64,
    alpha_s: &EIdx,
    lhs_s: &EIdx,
    rhs_s: &EIdx,
    l_a: &LIdx,
) -> Result<(), CheckError> {
    match core::infer_type_core(st, mode, fe_self, core::CHECK_FUEL, depth, lhs_s) {
        Err(e) => Err(e),
        Ok(tl) => {
            match core::is_def_eq_core(st, mode, fe_self, core::CHECK_FUEL, depth, &tl, alpha_s) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::not_implemented(code_points(&M_IOTA_LHS))),
                Ok(true) => {
                    match core::infer_type_core(st, mode, fe_self, core::CHECK_FUEL, depth, rhs_s) {
                        Err(e) => Err(e),
                        Ok(tr) => match core::is_def_eq_core(
                            st,
                            mode,
                            fe_self,
                            core::CHECK_FUEL,
                            depth,
                            &tr,
                            alpha_s,
                        ) {
                            Err(e) => Err(e),
                            Ok(false) => {
                                fail(core_types::not_implemented(code_points(&M_IOTA_RHS)))
                            }
                            Ok(true) => check_iota_slot_ty(st, mode, fe_self, depth, alpha_s, l_a),
                        },
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:31-53 checkIotaSidesTy
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:129-134 checkIotaSidesTy`
/// — the TT-lane slot-sort certification, split off so that the
/// `if mode.ttChecks` branch is one call.
pub fn check_iota_slot_ty(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    depth: u64,
    alpha_s: &EIdx,
    l_a: &LIdx,
) -> Result<(), CheckError> {
    if !con_ron_core::kernel::env::tt_checks(mode) {
        Ok(())
    } else {
        match core::infer_type_core(st, mode, fe_self, core::CHECK_FUEL, depth, alpha_s) {
            Err(e) => Err(e),
            Ok(ta) => match intern_e(st, ENodeView::Sort(l_a.dup2())) {
                Err(e) => Err(e),
                Ok(s) => {
                    match core::is_def_eq_core(st, mode, fe_self, core::CHECK_FUEL, depth, &ta, &s)
                    {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::not_implemented(code_points(&M_IOTA_SLOT))),
                        Ok(true) => Ok(()),
                    }
                }
            },
        }
    }
}

/// con-leche: none — `(cvName.str "_model").str ("iota_" ++ toString j)`, interned
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:138-140 iotaThmName`
/// — the name of a recursor's `j`-th model iota theorem.  `toString j` is
/// `con_ron_core::kernel::core_k::nat_to_dec`, the port's own decimal
/// recursion.
pub fn iota_thm_name(st: &mut AState, cv_name: &NIdx, j: u64) -> Result<NIdx, CheckError> {
    const IOTA_: [u32; 5] = [105, 111, 116, 97, 95];
    match ind_base::model_name(st, cv_name) {
        Err(e) => Err(e),
        Ok(m) => {
            let digits: Vec<u32> = core_k::nat_to_dec(j);
            let s: Vec<u32> = code_points_from(&digits, 0, code_points(&IOTA_));
            intern_n_node(st, NNodeView::Str(m, s))
        }
    }
}

/// con-leche: none — `xs.getLastD b0` over a `Vec<EIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:182 checkIotaThm` —
/// the major premise is the argument spine's last entry.
pub fn last_d_eidx(xs: &Vec<EIdx>, dflt: &EIdx) -> EIdx {
    if xs.is_empty() {
        dflt.dup2()
    } else {
        xs[xs.len() - 1].dup2()
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:148-166 checkIotaThm`
/// — the prologue both statement checks share: the stored `iota_j` theorem,
/// its level parameters, its telescope opened at free variables, and the
/// equation the body must be.  Returns the opened variables, the equation's
/// three arguments and the head's level.
pub fn iota_stmt_open(
    st: &mut AState,
    fe2: &IFEnv,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    depth: u64,
    j: u64,
) -> Result<(Vec<EIdx>, Vec<EIdx>, LIdx), CheckError> {
    match iota_thm_name(st, cv_name, j) {
        Err(e) => Err(e),
        Ok(tn) => match ind_base::find_cv(st, fe2, &tn) {
            Err(e) => Err(e),
            Ok(o) => {
                match ind_base::unwrap_or(o, core_types::not_implemented(code_points(&M_IOTA_MISS)))
                {
                    Err(e) => Err(e),
                    Ok(cvt) => {
                        if !core::nidx_vec_beq(&cvt.level_params, lps) {
                            fail(core_types::not_implemented(code_points(&M_IOTA_LPS)))
                        } else {
                            iota_stmt_open_at(st, depth, &cvt.ty)
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:155-166 checkIotaThm`
/// — the prologue's tail: the telescope, the equation head and its arity.
pub fn iota_stmt_open_at(
    st: &mut AState,
    depth: u64,
    tty: &EIdx,
) -> Result<(Vec<EIdx>, Vec<EIdx>, LIdx), CheckError> {
    match ind_base::open_pis_at_fvars_f(st, depth, tty, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_SHAPE))),
        Ok(Some(q)) => match expr_ops::get_app_args(st, CORE_WALK_FUEL, &q.1) {
            Err(e) => Err(e),
            Ok(targs) => match expr_ops::get_app_fn(st, CORE_WALK_FUEL, &q.1) {
                Err(e) => Err(e),
                Ok(tfn) => match ind_base::is_eq_head(st, &tfn) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::not_implemented(code_points(&M_IOTA_NOT_EQ))),
                    Ok(true) => {
                        if targs.len() != 3 {
                            fail(core_types::not_implemented(code_points(&M_IOTA_NOT_EQ)))
                        } else {
                            match ind_base::eq_head_level(st, &tfn) {
                                Err(e) => Err(e),
                                Ok(l_a) => Ok((q.0, targs, l_a)),
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:172-181 checkIotaThm`
/// — the left side's **head, arity and prefix** pins, shared by the plain and
/// the nested statement checks: the renamed recursor applied to the opened
/// prefix variables, `mI + 1` arguments in all.  The twin fails each of the
/// three with its own `s!` message; con-ron-core merges them into one, and so
/// does this (the module note).
pub fn iota_lhs_prefix_ok(
    st: &mut AState,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    m_i: u64,
    r_p: u64,
    fvs: &Vec<EIdx>,
    lfn: &EIdx,
    largs: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match struct_parts::param_levels(st, lps) {
        Err(e) => Err(e),
        Ok(lus) => {
            let rn: NIdx = f.rename(cv_name);
            match intern_e(st, ENodeView::Const(rn, lus)) {
                Err(e) => Err(e),
                Ok(want_hd) => {
                    if !lfn.eq2(&want_hd) {
                        Ok(false)
                    } else if largs.len() as u64 != m_i + 1 {
                        Ok(false)
                    } else {
                        let a: Vec<EIdx> = expr_ops::take_eidx(largs, r_p as usize);
                        let b: Vec<EIdx> = expr_ops::take_eidx(fvs, r_p as usize);
                        Ok(ind_base::eidx_vec_beq(&a, &b))
                    }
                }
            }
        }
    }
}
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:144-225 checkIotaThm`
/// — check a *canonical* recursor rule's `iota_j` theorem, semantically: the
/// stored theorem's telescope is opened at free variables, its body must be an
/// `Eq`, the equation's left side is structurally the renamed recursor applied
/// to the opened variables and a canonical major, and the right side is
/// definitionally the rule's applied right-hand side.
pub fn check_iota_thm(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &IRecRule,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
) -> Result<(), CheckError> {
    let depth: u64 = r_p + cn_f;
    match iota_stmt_open(st, fe2, cv_name, lps, depth, j) {
        Err(e) => Err(e),
        Ok(oq) => {
            let fvs: Vec<EIdx> = oq.0;
            let targs: Vec<EIdx> = oq.1;
            let l_a: LIdx = oq.2;
            match intern_e(st, ENodeView::BVar(0)) {
                Err(e) => Err(e),
                Ok(b0) => {
                    let lhs_s: EIdx = core::get_d_eidx(&targs, 1, &b0);
                    let rhs_s: EIdx = core::get_d_eidx(&targs, 2, &b0);
                    let x_fvs: Vec<EIdx> = core::drop_eidx(&fvs, r_p as usize);
                    match expr_ops::get_app_args(st, CORE_WALK_FUEL, &lhs_s) {
                        Err(e) => Err(e),
                        Ok(largs) => match expr_ops::get_app_fn(st, CORE_WALK_FUEL, &lhs_s) {
                            Err(e) => Err(e),
                            Ok(lfn) => match iota_lhs_prefix_ok(
                                st, f, cv_name, lps, m_i, r_p, &fvs, &lfn, &largs,
                            ) {
                                Err(e) => Err(e),
                                Ok(false) => {
                                    fail(core_types::not_implemented(code_points(&M_IOTA_HEAD)))
                                }
                                Ok(true) => match check_iota_major(
                                    st, f, r, cvj, cn_p, &fvs, &x_fvs, &largs, &b0,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(false) => {
                                        fail(core_types::not_implemented(code_points(&M_IOTA_MAJ)))
                                    }
                                    Ok(true) => check_iota_thm_ctor(
                                        st, mode, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, cn_f,
                                        rhs_a, &fvs, &x_fvs, &largs, &targs, &rhs_s, &l_a, &b0,
                                    ),
                                },
                            },
                        },
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:182-187 checkIotaThm`
/// — the major premise is the renamed constructor at its own level parameters,
/// applied to the leading parameter variables and the field variables.
pub fn check_iota_major(
    st: &mut AState,
    f: &RenameBy,
    r: &IRecRule,
    cvj: &IConstantVal,
    cn_p: u64,
    fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    largs: &Vec<EIdx>,
    b0: &EIdx,
) -> Result<bool, CheckError> {
    let major: EIdx = last_d_eidx(largs, b0);
    match struct_parts::param_levels(st, &cvj.level_params) {
        Err(e) => Err(e),
        Ok(cus) => {
            let rn: NIdx = f.rename(&r.ctor);
            match intern_e(st, ENodeView::Const(rn, cus)) {
                Err(e) => Err(e),
                Ok(c_hd) => {
                    let spine: Vec<EIdx> =
                        core::append_eidx(expr_ops::take_eidx(fvs, cn_p as usize), x_fvs);
                    match expr_ops::mk_app_n(st, &c_hd, &spine) {
                        Err(e) => Err(e),
                        Ok(want) => Ok(major.eq2(&want)),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:188-205 checkIotaThm`
/// — the constructor-telescope half: the constructor's telescope (renamed),
/// instantiated at the major's arguments, gives the field domains and the
/// canonical index tuple, both compared definitionally; then the statement's
/// prefix domains against the recursor's (renamed).
pub fn check_iota_thm_ctor(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    largs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
) -> Result<(), CheckError> {
    let depth: u64 = r_p + cn_f;
    match expr_ops::strip_pis(st, cn_p + cn_f, &cvj.ty) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_CTELE))),
        Ok(Some(_)) => match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, &cvj.ty) {
            Err(e) => Err(e),
            Ok(cty_r) => {
                let spine: Vec<EIdx> =
                    core::append_eidx(expr_ops::take_eidx(fvs, cn_p as usize), x_fvs);
                match expr_ops::inst_pis_at_f(st, CORE_WALK_FUEL, &spine, &cty_r) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_CTELE))),
                    Ok(Some(cq)) => check_iota_thm_idx(
                        st, mode, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, depth, rhs_a, fvs, x_fvs,
                        largs, targs, rhs_s, l_a, b0, &cq.0, &cq.1,
                    ),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:196-205 checkIotaThm`
/// — the index tuple's arity, the two index/domain comparisons and the
/// statement's prefix domains against the renamed recursor's.
pub fn check_iota_thm_idx(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    depth: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    largs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    cdoms: &Vec<EIdx>,
    cres: &EIdx,
) -> Result<(), CheckError> {
    let k: u64 = sub_nat(m_i, r_p);
    match expr_ops::get_app_args(st, CORE_WALK_FUEL, cres) {
        Err(e) => Err(e),
        Ok(cargs) => {
            if cargs.len() as u64 != cn_p + k {
                fail(core_types::not_implemented(code_points(&M_IOTA_CIDX)))
            } else {
                let lidx: Vec<EIdx> =
                    expr_ops::take_eidx(&core::drop_eidx(largs, r_p as usize), k as usize);
                let cidx: Vec<EIdx> = core::drop_eidx(&cargs, cn_p as usize);
                match ind_base::check_def_eq_list(st, mode, fe_self, depth, &lidx, &cidx) {
                    Err(e) => Err(e),
                    Ok(()) => match ind_base::fvar_type_ds(st, x_fvs) {
                        Err(e) => Err(e),
                        Ok(xdoms) => {
                            let cdom_tail: Vec<EIdx> = core::drop_eidx(cdoms, cn_p as usize);
                            match ind_base::check_def_eq_list(
                                st, mode, fe_self, depth, &xdoms, &cdom_tail,
                            ) {
                                Err(e) => Err(e),
                                Ok(()) => check_iota_thm_prefix(
                                    st, mode, fe_self, f, ty_a, r_p, cvj, cn_p, depth, rhs_a, fvs,
                                    targs, rhs_s, l_a, b0,
                                ),
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:201-205 checkIotaThm`
/// — the statement's prefix domains are the recursor's (renamed).
pub fn check_iota_thm_prefix(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    depth: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
) -> Result<(), CheckError> {
    match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, ty_a) {
        Err(e) => Err(e),
        Ok(ty_ar) => {
            let pfx: Vec<EIdx> = expr_ops::take_eidx(fvs, r_p as usize);
            match expr_ops::inst_pis_at_f(st, CORE_WALK_FUEL, &pfx, &ty_ar) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_RTELE))),
                Ok(Some(rq)) => match ind_base::fvar_type_ds(st, &pfx) {
                    Err(e) => Err(e),
                    Ok(pdoms) => {
                        match ind_base::check_def_eq_list(st, mode, fe_self, depth, &pdoms, &rq.0) {
                            Err(e) => Err(e),
                            Ok(()) => check_iota_thm_frames(
                                st, mode, fe_self, f, ty_a, r_p, cvj, cn_p, depth, rhs_a, fvs,
                                targs, rhs_s, l_a, b0,
                            ),
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:206-218 checkIotaThm`
/// — the rule's λ-domains are the public recursor prefix and the constructor's
/// field domains: the recursor's telescope is opened afresh at `rP` variables,
/// the constructor's is instantiated at the first `cnP` of them and then opened
/// at `cnF` more.  `cnF` is `depth - rP`, which is how the twin's `depth` was
/// built.
pub fn check_iota_thm_frames(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    depth: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
) -> Result<(), CheckError> {
    let cn_f: u64 = sub_nat(depth, r_p);
    match ind_base::open_pis_at_fvars_f(st, r_p, ty_a, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_RTELE))),
        Ok(Some(pq)) => {
            let fvs_p: Vec<EIdx> = pq.0;
            let pfx: Vec<EIdx> = expr_ops::take_eidx(&fvs_p, cn_p as usize);
            match expr_ops::inst_pis_at_f(st, CORE_WALK_FUEL, &pfx, &cvj.ty) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_CTELE))),
                Ok(Some(cq)) => match ind_base::fvar_type_ds(st, &pfx) {
                    Err(e) => Err(e),
                    Ok(pdoms) => {
                        match ind_base::check_def_eq_list(st, mode, fe_self, depth, &pdoms, &cq.0) {
                            Err(e) => Err(e),
                            Ok(()) => match ind_base::open_pis_at_fvars_f(st, cn_f, &cq.1, r_p) {
                                Err(e) => Err(e),
                                Ok(None) => {
                                    fail(core_types::not_implemented(code_points(&M_IOTA_CTELE)))
                                }
                                Ok(Some(xq)) => {
                                    let all: Vec<EIdx> = core::append_eidx(fvs_p, &xq.0);
                                    check_iota_thm_lams(
                                        st, mode, fe_self, f, depth, rhs_a, fvs, targs, rhs_s, l_a,
                                        b0, &all,
                                    )
                                }
                            },
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:216-218 checkIotaThm`
/// — the rule's λ-domains against the opened frame.
pub fn check_iota_thm_lams(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    depth: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    all: &Vec<EIdx>,
) -> Result<(), CheckError> {
    match expr_ops::inst_lams_at_f(st, CORE_WALK_FUEL, all, rhs_a) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_RULE))),
        Ok(Some(lq)) => match ind_base::fvar_type_ds(st, all) {
            Err(e) => Err(e),
            Ok(ldoms) => {
                match ind_base::check_def_eq_list(st, mode, fe_self, depth, &ldoms, &lq.0) {
                    Err(e) => Err(e),
                    Ok(()) => check_iota_thm_rhs(
                        st, mode, fe_self, f, depth, rhs_a, fvs, targs, rhs_s, l_a, b0,
                    ),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:55-149 checkIotaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:219-225 checkIotaThm`
/// — the right side is definitionally the rule's renamed right-hand side
/// applied to the whole opened frame, and both sides inhabit the type slot.
pub fn check_iota_thm_rhs(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    depth: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
) -> Result<(), CheckError> {
    match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, rhs_a) {
        Err(e) => Err(e),
        Ok(rhs_r) => match expr_ops::mk_app_n(st, &rhs_r, fvs) {
            Err(e) => Err(e),
            Ok(applied) => {
                match core::is_def_eq_core(
                    st,
                    mode,
                    fe_self,
                    core::CHECK_FUEL,
                    depth,
                    rhs_s,
                    &applied,
                ) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::not_implemented(code_points(&M_IOTA_MIS))),
                    Ok(true) => {
                        let alpha: EIdx = core::get_d_eidx(targs, 0, b0);
                        let lhs_s: EIdx = core::get_d_eidx(targs, 1, b0);
                        check_iota_sides_ty(st, mode, fe_self, depth, &alpha, &lhs_s, rhs_s, l_a)
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The nested-auxiliary statement (`Modeled.lean:227-356` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:232-262 nestedRuleShape`
/// — the nested-shape data of a non-canonical rule: the constructor's level and
/// parameter instantiations, read off the recursor type's major-premise domain.
/// The level list is a `Vec<LIdx>`, the shape `IRecRuleFire::Nested` stores.
pub fn nested_rule_shape(
    st: &mut AState,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
    j: u64,
) -> Result<Option<(Vec<LIdx>, Vec<EIdx>)>, CheckError> {
    match iota_thm_name(st, cv_name, j) {
        Err(e) => Err(e),
        Ok(thm) => match ind_base::find_cv(st, fe2, &thm) {
            Err(e) => Err(e),
            Ok(o) => {
                if !(o.is_some() && r_p <= m_i) {
                    Ok(None)
                } else {
                    nested_rule_shape_at(st, fe_self, lps, ty_a, m_i, r_p, cn_p)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:236-262 nestedRuleShape`
/// — the major premise's domain, its head's level arguments, and the
/// parameter pins lowered out of the index frame.
pub fn nested_rule_shape_at(
    st: &mut AState,
    fe_self: &IFEnv,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
) -> Result<Option<(Vec<LIdx>, Vec<EIdx>)>, CheckError> {
    match expr_ops::strip_pis(st, m_i, ty_a) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(q)) => match view(st, &q.1) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, _, _)) => {
                match expr_ops::get_app_fn(st, CORE_WALK_FUEL, &dom) {
                    Err(e) => Err(e),
                    Ok(hd) => match view(st, &hd) {
                        Err(e) => Err(e),
                        Ok(ENodeView::Const(_, lvls_idx)) => nested_rule_shape_args(
                            st, fe_self, lps, m_i, r_p, cn_p, &dom, &lvls_idx,
                        ),
                        Ok(_) => Ok(None),
                    },
                }
            }
            Ok(_) => Ok(None),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:241-259 nestedRuleShape`
/// — the domain's argument spine: the leading `cnP` are the pins, lowered out
/// of the `k` index binders and lifted back to compare, the trailing `k` are
/// the index spine, and the pins are scoped, resolving and level-closed.
pub fn nested_rule_shape_args(
    st: &mut AState,
    fe_self: &IFEnv,
    lps: &Vec<NIdx>,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
    dom: &EIdx,
    lvls_idx: &LsIdx,
) -> Result<Option<(Vec<LIdx>, Vec<EIdx>)>, CheckError> {
    let k: u64 = sub_nat(m_i, r_p);
    match expr_ops::get_app_args(st, CORE_WALK_FUEL, dom) {
        Err(e) => Err(e),
        Ok(args) => {
            let head: Vec<EIdx> = expr_ops::take_eidx(&args, cn_p as usize);
            match lower_bvars_list(st, k, &head, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(pins) => match lift_bvars_list(st, k, &pins, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(lifted) => match struct_parts::bvars_desc(st, k) {
                        Err(e) => Err(e),
                        Ok(idx_spine) => match crate::arena::monad::read_names(st, lps) {
                            Err(e) => Err(e),
                            Ok(ks) => match view_ls(st, lvls_idx) {
                                Err(e) => Err(e),
                                Ok(lvls) => match crate::arena::monad::read_levels(st, lvls_idx) {
                                    Err(e) => Err(e),
                                    Ok(lvl_vals) => {
                                        match nested_pins_ok(st, fe_self, lps, r_p, &pins, 0) {
                                            Err(e) => Err(e),
                                            Ok(pins_ok) => {
                                                if args.len() as u64 == cn_p + k
                                                    && ind_base::eidx_vec_beq(&head, &lifted)
                                                    && ind_base::eidx_vec_beq(
                                                        &core::drop_eidx(&args, cn_p as usize),
                                                        &idx_spine,
                                                    )
                                                    && pins_ok
                                                    && ind_base::levels_all_params_defined(
                                                        &ks, &lvl_vals, 0,
                                                    )
                                                {
                                                    Ok(Some((lvls, pins)))
                                                } else {
                                                    Ok(None)
                                                }
                                            }
                                        }
                                    }
                                },
                            },
                        },
                    },
                },
            }
        }
    }
}

/// con-leche: none — `(args.take cnP).mapM (lowerBVarsFast coreWalkFuel k 0)`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:244 nestedRuleShape`
/// — the cursor recursion the `mapM` becomes (DESIGN.md §3.4).
pub fn lower_bvars_list(
    st: &mut AState,
    k: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let x: EIdx = xs[i].dup2();
        match expr_ops::lower_bvars_fast(st, CORE_WALK_FUEL, k, 0, &x) {
            Err(e) => Err(e),
            Ok(r) => {
                let mut o: Vec<EIdx> = out;
                o.push(r);
                lower_bvars_list(st, k, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: none — `pins.mapM (liftLooseBVarsFast coreWalkFuel k 0)`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:245 nestedRuleShape`
/// — the cursor recursion the `mapM` becomes.
pub fn lift_bvars_list(
    st: &mut AState,
    k: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let x: EIdx = xs[i].dup2();
        match expr_ops::lift_loose_bvars_fast(st, CORE_WALK_FUEL, k, 0, &x) {
            Err(e) => Err(e),
            Ok(r) => {
                let mut o: Vec<EIdx> = out;
                o.push(r);
                lift_bvars_list(st, k, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:151-190 nestedRuleShape
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:250-254 nestedRuleShape`
/// — each pin is fvar-free, scoped at the recursor prefix, resolving and
/// level-closed.  **All four conjuncts run for every pin**, as the twin's `do`
/// does (Lean lifts every `(← e)` out of the `&&`), and the walk stops at the
/// first pin that fails, which is `List.allM`.
pub fn nested_pins_ok(
    st: &mut AState,
    fe_self: &IFEnv,
    lps: &Vec<NIdx>,
    r_p: u64,
    pins: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= pins.len() {
        Ok(true)
    } else {
        let p: EIdx = pins[i].dup2();
        match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, &p) {
            Err(e) => Err(e),
            Ok(w1) => match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, r_p, &p) {
                Err(e) => Err(e),
                Ok(w2) => match ind_base::consts_resolve_f_fast(st, fe_self, &p) {
                    Err(e) => Err(e),
                    Ok(w3) => match ind_base::all_level_params_defined(st, lps, &p) {
                        Err(e) => Err(e),
                        Ok(w4) => {
                            if !w1 && w2 && w3 && w4 {
                                nested_pins_ok(st, fe_self, lps, r_p, pins, i + 1)
                            } else {
                                Ok(false)
                            }
                        }
                    },
                },
            },
        }
    }
}
/// con-leche: none — `pins.mapM fun p => instSpine … (← renameConsts f p)`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:293-295 checkIotaThmN`
/// — the cursor recursion the `mapM` becomes: each pin is renamed and then
/// instantiated at the opened recursor prefix, in that order.
pub fn inst_spine_list_renamed(
    st: &mut AState,
    f: &RenameBy,
    args: &Vec<EIdx>,
    t: u64,
    pins: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= pins.len() {
        Ok(out)
    } else {
        let p: EIdx = pins[i].dup2();
        match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, &p) {
            Err(e) => Err(e),
            Ok(pr) => match expr_ops::inst_spine(st, CORE_WALK_FUEL, args, t, &pr) {
                Err(e) => Err(e),
                Ok(r) => {
                    let mut o: Vec<EIdx> = out;
                    o.push(r);
                    inst_spine_list_renamed(st, f, args, t, pins, i + 1, o)
                }
            },
        }
    }
}

/// con-leche: none — `pins.mapM fun p => instSpine …`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:337 checkIotaThmN`
/// — the same cursor recursion without the renaming (the public frame's).
pub fn inst_spine_list(
    st: &mut AState,
    args: &Vec<EIdx>,
    t: u64,
    pins: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= pins.len() {
        Ok(out)
    } else {
        let p: EIdx = pins[i].dup2();
        match expr_ops::inst_spine(st, CORE_WALK_FUEL, args, t, &p) {
            Err(e) => Err(e),
            Ok(r) => {
                let mut o: Vec<EIdx> = out;
                o.push(r);
                inst_spine_list(st, args, t, pins, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:268-356 checkIotaThmN`
/// — check a *nested-auxiliary* recursor rule's `iota_j` theorem: the
/// generalization of `checkIotaThm` to rules whose constructor parameters and
/// levels are fixed instantiations.  A rule the nested shape does not
/// recognise is `.inert`, and the twin's closing `pure (.nested lvls pins)` is
/// this function's `Ok` — the whole check is the guard on it.
pub fn check_iota_thm_n(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &IRecRule,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
) -> Result<IRecRuleFire, CheckError> {
    match nested_rule_shape(st, fe2, fe_self, cv_name, lps, ty_a, m_i, r_p, cn_p, j) {
        Err(e) => Err(e),
        Ok(None) => Ok(IRecRuleFire::Inert),
        Ok(Some(sh)) => {
            let lvls: Vec<LIdx> = sh.0;
            let pins: Vec<EIdx> = sh.1;
            match check_iota_thm_n_at(
                st, mode, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, r, cvj, cn_p, cn_f,
                rhs_a, &lvls, &pins,
            ) {
                Err(e) => Err(e),
                Ok(()) => Ok(IRecRuleFire::Nested(lvls, pins)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:275-311 checkIotaThmN`
/// — the statement's prologue at a nested rule: the opened theorem, the pins
/// instantiated at the opened prefix, the left side's head/arity/prefix pins
/// and the major at the stored level instantiations.
pub fn check_iota_thm_n_at(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &IRecRule,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    lvls: &Vec<LIdx>,
    pins: &Vec<EIdx>,
) -> Result<(), CheckError> {
    let depth: u64 = r_p + cn_f;
    match iota_stmt_open(st, fe2, cv_name, lps, depth, j) {
        Err(e) => Err(e),
        Ok(oq) => {
            let fvs: Vec<EIdx> = oq.0;
            let targs: Vec<EIdx> = oq.1;
            let l_a: LIdx = oq.2;
            match intern_e(st, ENodeView::BVar(0)) {
                Err(e) => Err(e),
                Ok(b0) => {
                    let lhs_s: EIdx = core::get_d_eidx(&targs, 1, &b0);
                    let rhs_s: EIdx = core::get_d_eidx(&targs, 2, &b0);
                    let x_fvs: Vec<EIdx> = core::drop_eidx(&fvs, r_p as usize);
                    let pfx: Vec<EIdx> = expr_ops::take_eidx(&fvs, r_p as usize);
                    match inst_spine_list_renamed(st, f, &pfx, sub_nat(r_p, 1), pins, 0, Vec::new())
                    {
                        Err(e) => Err(e),
                        Ok(pins_f) => match expr_ops::get_app_args(st, CORE_WALK_FUEL, &lhs_s) {
                            Err(e) => Err(e),
                            Ok(largs) => match expr_ops::get_app_fn(st, CORE_WALK_FUEL, &lhs_s) {
                                Err(e) => Err(e),
                                Ok(lfn) => match iota_lhs_prefix_ok(
                                    st, f, cv_name, lps, m_i, r_p, &fvs, &lfn, &largs,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(false) => {
                                        fail(core_types::not_implemented(code_points(&M_IOTA_HEAD)))
                                    }
                                    Ok(true) => check_iota_thm_n_major(
                                        st, mode, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, cn_f,
                                        rhs_a, &fvs, &x_fvs, &largs, &targs, &rhs_s, &l_a, &b0,
                                        lvls, pins, &pins_f, r,
                                    ),
                                },
                            },
                        },
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:306-311 checkIotaThmN`
/// — the major premise at the STORED level instantiations, applied to the
/// instantiated pins and the field variables.
pub fn check_iota_thm_n_major(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    largs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    lvls: &Vec<LIdx>,
    pins: &Vec<EIdx>,
    pins_f: &Vec<EIdx>,
    r: &IRecRule,
) -> Result<(), CheckError> {
    let major: EIdx = last_d_eidx(largs, b0);
    match ind_base::intern_ls(st, lvls) {
        Err(e) => Err(e),
        Ok(lvls_idx) => {
            let rn: NIdx = f.rename(&r.ctor);
            match intern_e(st, ENodeView::Const(rn, lvls_idx.dup2())) {
                Err(e) => Err(e),
                Ok(c_hd) => {
                    let spine: Vec<EIdx> = core::append_eidx(env::eidx_vec_dup(pins_f), x_fvs);
                    match expr_ops::mk_app_n(st, &c_hd, &spine) {
                        Err(e) => Err(e),
                        Ok(want) => {
                            if !major.eq2(&want) {
                                fail(core_types::not_implemented(code_points(&M_IOTA_MAJ)))
                            } else {
                                check_iota_thm_n_ctor(
                                    st, mode, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, cn_f, rhs_a,
                                    fvs, x_fvs, largs, targs, rhs_s, l_a, b0, &lvls_idx, pins,
                                    pins_f,
                                )
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:312-322 checkIotaThmN`
/// — the constructor's telescope at the stored level instantiations (renamed),
/// instantiated at the pins and the field variables.
pub fn check_iota_thm_n_ctor(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    largs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    lvls_idx: &LsIdx,
    pins: &Vec<EIdx>,
    pins_f: &Vec<EIdx>,
) -> Result<(), CheckError> {
    match expr_ops::strip_pis(st, cn_p + cn_f, &cvj.ty) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_CTELE))),
        Ok(Some(q)) => match expr_ops::get_app_fn(st, CORE_WALK_FUEL, &q.1) {
            Err(e) => Err(e),
            Ok(hd) => match view(st, &hd) {
                Err(e) => Err(e),
                Ok(ENodeView::Const(_, _)) => {
                    match expr_ops::inst_lp_fast(
                        st,
                        CORE_WALK_FUEL,
                        &cvj.level_params,
                        lvls_idx,
                        &cvj.ty,
                    ) {
                        Err(e) => Err(e),
                        Ok(cty_l) => {
                            match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, &cty_l) {
                                Err(e) => Err(e),
                                Ok(cty_r) => {
                                    let spine: Vec<EIdx> =
                                        core::append_eidx(env::eidx_vec_dup(pins_f), x_fvs);
                                    match expr_ops::inst_pis_at_f(
                                        st,
                                        CORE_WALK_FUEL,
                                        &spine,
                                        &cty_r,
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(None) => fail(core_types::not_implemented(code_points(
                                            &M_IOTA_CTELE,
                                        ))),
                                        Ok(Some(cq)) => check_iota_thm_n_idx(
                                            st, mode, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, cn_f,
                                            rhs_a, fvs, x_fvs, largs, targs, rhs_s, l_a, b0,
                                            lvls_idx, pins, &cq.0, &cq.1,
                                        ),
                                    }
                                }
                            }
                        }
                    }
                }
                Ok(_) => fail(core_types::not_implemented(code_points(&M_IOTA_RHEAD))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:323-332 checkIotaThmN`
/// — the index tuple's arity, the two index/domain comparisons and the
/// statement's prefix domains against the renamed recursor's.
pub fn check_iota_thm_n_idx(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    largs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    lvls_idx: &LsIdx,
    pins: &Vec<EIdx>,
    cdoms: &Vec<EIdx>,
    cres: &EIdx,
) -> Result<(), CheckError> {
    let depth: u64 = r_p + cn_f;
    let k: u64 = sub_nat(m_i, r_p);
    match expr_ops::get_app_args(st, CORE_WALK_FUEL, cres) {
        Err(e) => Err(e),
        Ok(cargs) => {
            if cargs.len() as u64 != cn_p + k {
                fail(core_types::not_implemented(code_points(&M_IOTA_CIDX)))
            } else {
                let lidx: Vec<EIdx> =
                    expr_ops::take_eidx(&core::drop_eidx(largs, r_p as usize), k as usize);
                let cidx: Vec<EIdx> = core::drop_eidx(&cargs, cn_p as usize);
                match ind_base::check_def_eq_list(st, mode, fe_self, depth, &lidx, &cidx) {
                    Err(e) => Err(e),
                    Ok(()) => match ind_base::fvar_type_ds(st, x_fvs) {
                        Err(e) => Err(e),
                        Ok(xdoms) => {
                            let cdom_tail: Vec<EIdx> = core::drop_eidx(cdoms, cn_p as usize);
                            match ind_base::check_def_eq_list(
                                st, mode, fe_self, depth, &xdoms, &cdom_tail,
                            ) {
                                Err(e) => Err(e),
                                Ok(()) => check_iota_thm_n_prefix(
                                    st, mode, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, cn_f, rhs_a,
                                    fvs, targs, rhs_s, l_a, b0, lvls_idx, pins,
                                ),
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:328-332 checkIotaThmN`
/// — the statement's prefix domains are the recursor's (renamed).
pub fn check_iota_thm_n_prefix(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    lvls_idx: &LsIdx,
    pins: &Vec<EIdx>,
) -> Result<(), CheckError> {
    let depth: u64 = r_p + cn_f;
    match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, ty_a) {
        Err(e) => Err(e),
        Ok(ty_ar) => {
            let pfx: Vec<EIdx> = expr_ops::take_eidx(fvs, r_p as usize);
            match expr_ops::inst_pis_at_f(st, CORE_WALK_FUEL, &pfx, &ty_ar) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_RTELE))),
                Ok(Some(rq)) => match ind_base::fvar_type_ds(st, &pfx) {
                    Err(e) => Err(e),
                    Ok(pdoms) => {
                        match ind_base::check_def_eq_list(st, mode, fe_self, depth, &pdoms, &rq.0) {
                            Err(e) => Err(e),
                            Ok(()) => check_iota_thm_n_frames(
                                st, mode, fe_self, f, ty_a, m_i, r_p, cvj, cn_p, cn_f, rhs_a, fvs,
                                targs, rhs_s, l_a, b0, lvls_idx, pins,
                            ),
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:333-349 checkIotaThmN`
/// — the PUBLIC frame: the recursor's telescope opened afresh, the pins
/// instantiated there (annotated and typed against the constructor's domains
/// at the stored level instantiations), the constructor's fields opened, the
/// residual's arity, and the rule's λ-domains.
pub fn check_iota_thm_n_frames(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    lvls_idx: &LsIdx,
    pins: &Vec<EIdx>,
) -> Result<(), CheckError> {
    let depth: u64 = r_p + cn_f;
    match ind_base::open_pis_at_fvars_f(st, r_p, ty_a, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_RTELE))),
        Ok(Some(pq)) => {
            let fvs_p: Vec<EIdx> = pq.0;
            let pfx: Vec<EIdx> = expr_ops::take_eidx(&fvs_p, r_p as usize);
            match inst_spine_list(st, &pfx, sub_nat(r_p, 1), pins, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(pins_p) => match ind_base::check_annot_list(st, mode, fe_self, depth, &pins_p) {
                    Err(e) => Err(e),
                    Ok(()) => match expr_ops::inst_lp_fast(
                        st,
                        CORE_WALK_FUEL,
                        &cvj.level_params,
                        lvls_idx,
                        &cvj.ty,
                    ) {
                        Err(e) => Err(e),
                        Ok(cty_l2) => {
                            match expr_ops::inst_pis_at_f(st, CORE_WALK_FUEL, &pins_p, &cty_l2) {
                                Err(e) => Err(e),
                                Ok(None) => {
                                    fail(core_types::not_implemented(code_points(&M_IOTA_CTELE)))
                                }
                                Ok(Some(cq)) => match ind_base::check_typed_list(
                                    st, mode, fe_self, depth, &pins_p, &cq.0,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(()) => check_iota_thm_n_fields(
                                        st, mode, fe_self, f, m_i, r_p, cn_p, cn_f, rhs_a, fvs,
                                        targs, rhs_s, l_a, b0, &fvs_p, &cq.1,
                                    ),
                                },
                            }
                        }
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:192-317 checkIotaThmN
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:343-349 checkIotaThmN`
/// — the constructor's fields opened at the public frame, the residual's
/// arity, and the rule's λ-domains against the whole frame.
pub fn check_iota_thm_n_fields(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    f: &RenameBy,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
    cn_f: u64,
    rhs_a: &EIdx,
    fvs: &Vec<EIdx>,
    targs: &Vec<EIdx>,
    rhs_s: &EIdx,
    l_a: &LIdx,
    b0: &EIdx,
    fvs_p: &Vec<EIdx>,
    crest_p: &EIdx,
) -> Result<(), CheckError> {
    let depth: u64 = r_p + cn_f;
    match ind_base::open_pis_at_fvars_f(st, cn_f, crest_p, r_p) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_CTELE))),
        Ok(Some(xq)) => match expr_ops::get_app_args(st, CORE_WALK_FUEL, &xq.1) {
            Err(e) => Err(e),
            Ok(rargs) => {
                if rargs.len() as u64 != cn_p + sub_nat(m_i, r_p) {
                    fail(core_types::not_implemented(code_points(&M_IOTA_CARITY)))
                } else {
                    let all: Vec<EIdx> = core::append_eidx(env::eidx_vec_dup(fvs_p), &xq.0);
                    check_iota_thm_lams(
                        st, mode, fe_self, f, depth, rhs_a, fvs, targs, rhs_s, l_a, b0, &all,
                    )
                }
            }
        },
    }
}
// ---------------------------------------------------------------------------
// One rule, and the fold over a recursor's rules (`Modeled.lean:358-403`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:361-392 checkIotaRule`
/// — check one modeled recursor rule: generic well-formedness of the
/// right-hand side, then the model's `iota_j` theorem.
pub fn check_iota_rule(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &IRecRule,
) -> Result<IRecRule, CheckError> {
    let found: Option<IConstantInfo> = match env::ifenv_find(fe2, &r.ctor) {
        Some(ci) => Some(env::i_constant_info_dup(ci)),
        None => None,
    };
    match found {
        Some(IConstantInfo::CtorInfo(cvj, cn_p, cn_f)) => {
            if r.nfields != cn_f {
                fail(core_types::invalid(code_points(&M_RULE_NF)))
            } else {
                check_iota_rule_wf(
                    st, mode, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, r, &cvj, cn_p, cn_f,
                )
            }
        }
        _ => fail(core_types::invalid(code_points(&M_RULE_CTOR))),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:371-384 checkIotaRule`
/// — the right-hand side's generic well-formedness: scoped, annotated,
/// level-closed, resolving, a λ-telescope over the recursor prefix and the
/// constructor's fields, and typeable.
pub fn check_iota_rule_wf(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &IRecRule,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
) -> Result<IRecRule, CheckError> {
    match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, &r.rhs) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_RULE_BVAR))),
        Ok(true) => match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, &r.rhs) {
            Err(e) => Err(e),
            Ok(true) => fail(core_types::invalid(code_points(&M_RULE_FVAR))),
            Ok(false) => {
                match core::annotate_core(st, mode, fe_self, core::CHECK_FUEL, 0, &r.rhs) {
                    Err(e) => Err(e),
                    Ok(rhs_a) => check_iota_rule_fire(
                        st, mode, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, r, cvj, cn_p,
                        cn_f, rhs_a,
                    ),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:376-392 checkIotaRule`
/// — the annotated right-hand side's guards, and then **the firing mode,
/// computed once and stored on the rule**: a canonical rule takes the plain
/// statement check, a non-canonical one the nested check (which answers
/// `.inert` where it does not recognise the shape).
pub fn check_iota_rule_fire(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    j: u64,
    r: &IRecRule,
    cvj: &IConstantVal,
    cn_p: u64,
    cn_f: u64,
    rhs_a: EIdx,
) -> Result<IRecRule, CheckError> {
    match ind_base::all_level_params_defined(st, lps, &rhs_a) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_RULE_LPS))),
        Ok(true) => match ind_base::consts_resolve_f_fast(st, fe_self, &rhs_a) {
            Err(e) => Err(e),
            Ok(false) => match ind_base::unresolved_consts_error(st, &rhs_a) {
                Err(e) => Err(e),
                Ok(er) => fail(er),
            },
            Ok(true) => match expr_ops::strip_lams(st, r_p + cn_f, &rhs_a) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::not_implemented(code_points(&M_IOTA_RULE))),
                Ok(Some(_)) => {
                    match core::infer_type_core(st, mode, fe_self, core::CHECK_FUEL, 0, &rhs_a) {
                        Err(e) => Err(e),
                        Ok(_rhs_ty) => {
                            match expr_ops::rec_rule_plain(st, CORE_WALK_FUEL, ty_a, m_i, r_p, cn_p)
                            {
                                Err(e) => Err(e),
                                Ok(true) => match check_iota_thm(
                                    st, mode, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, r,
                                    cvj, cn_p, cn_f, &rhs_a,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(()) => check_iota_rule_bits(
                                        st,
                                        fe2,
                                        cv_name,
                                        r,
                                        cn_p,
                                        rhs_a,
                                        IRecRuleFire::Plain,
                                    ),
                                },
                                Ok(false) => match check_iota_thm_n(
                                    st, mode, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, r,
                                    cvj, cn_p, cn_f, &rhs_a,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(fire) => {
                                        check_iota_rule_bits(st, fe2, cv_name, r, cn_p, rhs_a, fire)
                                    }
                                },
                            }
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:319-360 checkIotaRule
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:391-392 checkIotaRule`
/// — the stored rule: `{ r with rhs := rhsA, ctorParams := cnP, fire,
/// paramsBlind := false }`, with the two rescue bits stamped by `recRuleBits`.
pub fn check_iota_rule_bits(
    st: &mut AState,
    fe2: &IFEnv,
    cv_name: &NIdx,
    r: &IRecRule,
    cn_p: u64,
    rhs_a: EIdx,
    fire: IRecRuleFire,
) -> Result<IRecRule, CheckError> {
    let rl = IRecRule {
        ctor: r.ctor.dup2(),
        nfields: r.nfields,
        ctor_params: cn_p,
        fire,
        rhs: rhs_a,
        k: r.k,
        eta: r.eta,
        params_blind: false,
    };
    core::rec_rule_bits(st, fe2, cv_name, rl)
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:362-371 checkIotaRules
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:396-403 checkIotaRules`
/// — the per-rule check, folded over a modeled recursor's rules.  Lean conses
/// on the way out; the port pushes on the way in, at the same order of
/// effects.
pub fn check_iota_rules(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    cv_name: &NIdx,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    j: u64,
    rules: &Vec<IRecRule>,
    i: usize,
    out: Vec<IRecRule>,
) -> Result<Vec<IRecRule>, CheckError> {
    if i >= rules.len() {
        Ok(out)
    } else {
        match check_iota_rule(
            st, mode, fe2, fe_self, f, cv_name, lps, ty_a, m_i, r_p, j, &rules[i],
        ) {
            Err(e) => Err(e),
            Ok(r2) => {
                let mut o: Vec<IRecRule> = out;
                o.push(r2);
                check_iota_rules(
                    st,
                    mode,
                    fe2,
                    fe_self,
                    f,
                    cv_name,
                    lps,
                    ty_a,
                    m_i,
                    r_p,
                    j + 1,
                    rules,
                    i + 1,
                    o,
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The block's members (`Modeled.lean:405-495` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:409-430 checkMemberVal`
/// — check a block member's constant against its `_model` counterpart.
pub fn check_member_val(
    st: &mut AState,
    mode: &CheckMode,
    block_names: &Vec<NIdx>,
    fe2: &IFEnv,
    cv: &IConstantVal,
) -> Result<IConstantVal, CheckError> {
    match block_rename_table(st, block_names) {
        Err(e) => Err(e),
        Ok(f) => match ind_base::check_constant_val(st, mode, fe2, cv) {
            Err(e) => Err(e),
            Ok(cv_a) => match read_name(st, &cv_a.name) {
                Err(e) => Err(e),
                Ok(an) => {
                    if level::name_is_model_suffix(&an) {
                        fail(core_types::invalid(code_points(&M_MODEL_NAME)))
                    } else {
                        check_member_model(st, &f, fe2, cv_a)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:373-401 checkMemberVal
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:418-430 checkMemberVal`
/// — the model counterpart: it exists, at the member's level parameters, and
/// its type is the member's under the block renaming.
pub fn check_member_model(
    st: &mut AState,
    f: &RenameBy,
    fe2: &IFEnv,
    cv_a: IConstantVal,
) -> Result<IConstantVal, CheckError> {
    match ind_base::model_name(st, &cv_a.name) {
        Err(e) => Err(e),
        Ok(mn) => {
            let found: Option<IConstantInfo> = match env::ifenv_find(fe2, &mn) {
                Some(ci) => Some(env::i_constant_info_dup(ci)),
                None => None,
            };
            match found {
                Some(IConstantInfo::DefnInfo(cvm, _, _)) => {
                    if !core::nidx_vec_beq(&cvm.level_params, &cv_a.level_params) {
                        fail(core_types::not_implemented(code_points(&M_MODEL_LPS)))
                    } else {
                        match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, f, &cv_a.ty) {
                            Err(e) => Err(e),
                            Ok(renamed) => {
                                if renamed.eq2(&cvm.ty) {
                                    Ok(cv_a)
                                } else {
                                    fail(core_types::not_implemented(code_points(&M_MODEL_TY)))
                                }
                            }
                        }
                    }
                }
                _ => fail(core_types::not_implemented(code_points(&M_NO_ROUTE))),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:403-414 checkIndMember
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:435-443 checkIndMember`
/// — check and install one non-recursor member of a modeled inductive block
/// against its `_model` counterpart.
pub fn check_ind_member(
    st: &mut AState,
    mode: &CheckMode,
    block_names: &Vec<NIdx>,
    caps: &IIndCaps,
    fe2: IFEnv,
    ci: &IConstantInfo,
) -> Result<IFEnv, CheckError> {
    match env::i_constant_info_to_constant_val(&mut st.store, ci) {
        Err(e) => Err(e),
        Ok(cv) => match check_member_val(st, mode, block_names, &fe2, &cv) {
            Err(e) => Err(e),
            Ok(cv_a) => match ci {
                IConstantInfo::IndInfo(_, _) => Ok(env::ifenv_push(
                    fe2,
                    IConstantInfo::IndInfo(cv_a, env::i_ind_caps_dup(caps)),
                )),
                IConstantInfo::CtorInfo(_, n_p, n_f) => Ok(env::ifenv_push(
                    fe2,
                    IConstantInfo::CtorInfo(cv_a, *n_p, *n_f),
                )),
                _ => fail(core_types::invalid(code_points(&M_NONIND))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:448-453 checkIndMembers`
/// — the member fold, as an explicit recursion (DESIGN.md §3.4: a `foldlM`
/// with a partially applied step is a helper of its own).
pub fn check_ind_members(
    st: &mut AState,
    mode: &CheckMode,
    block_names: &Vec<NIdx>,
    caps: &IIndCaps,
    fe: IFEnv,
    nonrecs: &Vec<IConstantInfo>,
    i: usize,
) -> Result<IFEnv, CheckError> {
    if i >= nonrecs.len() {
        Ok(fe)
    } else {
        match check_ind_member(st, mode, block_names, caps, fe, &nonrecs[i]) {
            Err(e) => Err(e),
            Ok(fe2) => check_ind_members(st, mode, block_names, caps, fe2, nonrecs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:416-433 provisionRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:458-469 provisionRecs`
/// — phase 0 of the recursor group: check each recursor's constant and
/// provision it *rule-less* on top of the previous ones.  Lean conses the
/// checked record on the way out; the port pushes on the way in, at the same
/// order of effects.
pub fn provision_recs(
    st: &mut AState,
    mode: &CheckMode,
    block_names: &Vec<NIdx>,
    fe_acc: IFEnv,
    recs: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
) -> Result<(IFEnv, Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>), CheckError> {
    if i >= recs.len() {
        Ok((fe_acc, out))
    } else {
        match &recs[i] {
            IConstantInfo::RecInfo(_, m_i, r_p, rules) => {
                let m: u64 = *m_i;
                let rp: u64 = *r_p;
                let rl: Vec<IRecRule> = env::i_rec_rules_dup(rules);
                match env::i_constant_info_to_constant_val(&mut st.store, &recs[i]) {
                    Err(e) => Err(e),
                    Ok(cv) => match check_member_val(st, mode, block_names, &fe_acc, &cv) {
                        Err(e) => Err(e),
                        Ok(cv_a) => {
                            let stored = IConstantInfo::RecInfo(
                                env::i_constant_val_dup(&cv_a),
                                m,
                                rp,
                                Vec::new(),
                            );
                            let mut o: Vec<(IConstantVal, u64, u64, Vec<IRecRule>)> = out;
                            o.push((cv_a, m, rp, rl));
                            provision_recs(
                                st,
                                mode,
                                block_names,
                                env::ifenv_push(fe_acc, stored),
                                recs,
                                i + 1,
                                o,
                            )
                        }
                    },
                }
            }
            _ => fail(core_types::not_implemented(code_points(&M_ORDER))),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:473-479 installIndRecs`
/// — the install fold, as an explicit recursion.
pub fn install_ind_recs(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    f: &RenameBy,
    acc: IFEnv,
    checked: &Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
    i: usize,
) -> Result<IFEnv, CheckError> {
    if i >= checked.len() {
        Ok(acc)
    } else {
        let c: &(IConstantVal, u64, u64, Vec<IRecRule>) = &checked[i];
        match check_iota_rules(
            st,
            mode,
            fe2,
            fe_self,
            f,
            &c.0.name,
            &c.0.level_params,
            &c.0.ty,
            c.1,
            c.2,
            0,
            &c.3,
            0,
            Vec::new(),
        ) {
            Err(e) => Err(e),
            Ok(rules2) => {
                let stored =
                    IConstantInfo::RecInfo(env::i_constant_val_dup(&c.0), c.1, c.2, rules2);
                install_ind_recs(
                    st,
                    mode,
                    fe2,
                    fe_self,
                    f,
                    env::ifenv_push(acc, stored),
                    checked,
                    i + 1,
                )
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:485-495 checkIndRecs`
/// — check and install a block's recursors *as a group*: every rule right-hand
/// side may mention any of them, so all are provisioned rule-less together and
/// installed together.  The twin uses `fe₂` four times; Lean's value semantics
/// copies it for free and the port pays two `ifenv_dup`s, which is what
/// `con_ron_core`'s `fenv::dup` costs at the same site.
pub fn check_ind_recs(
    st: &mut AState,
    mode: &CheckMode,
    block_names: &Vec<NIdx>,
    fe2: IFEnv,
    recs: &Vec<IConstantInfo>,
) -> Result<IFEnv, CheckError> {
    if recs.is_empty() {
        Ok(fe2)
    } else {
        match block_rename_table(st, block_names) {
            Err(e) => Err(e),
            Ok(f) => match eq_basis_stored(st, &fe2) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::not_implemented(code_points(&M_EQ_BASIS))),
                Ok(true) => {
                    let fe_env: IFEnv = ind_base::ifenv_dup(&fe2);
                    match provision_recs(
                        st,
                        mode,
                        block_names,
                        ind_base::ifenv_dup(&fe2),
                        recs,
                        0,
                        Vec::new(),
                    ) {
                        Err(e) => Err(e),
                        Ok(pq) => install_ind_recs(st, mode, &fe_env, &pq.0, &f, fe2, &pq.1, 0),
                    }
                }
            },
        }
    }
}
// ---------------------------------------------------------------------------
// The projection functions (`Modeled.lean:497-599` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:501-517 checkProjLookups`
/// — stage 1 of `checkProjFn`: the stored constants the projection depends on.
pub fn check_proj_lookups(
    st: &mut AState,
    fe2: &IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> Result<(IConstantVal, IConstantVal), CheckError> {
    let found: Option<IConstantInfo> = match env::ifenv_find(fe2, ctor_name) {
        Some(ci) => Some(env::i_constant_info_dup(ci)),
        None => None,
    };
    match found {
        Some(IConstantInfo::CtorInfo(cvj, cn_p, cn_f)) => {
            if !(cn_p == n_p && cn_f == n_f) {
                fail(core_types::not_implemented(code_points(&M_PL_ARITY)))
            } else {
                check_proj_lookups_model(st, fe2, t, lps, i, cvj)
            }
        }
        _ => fail(core_types::not_implemented(code_points(&M_PL_CTOR))),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:507-517 checkProjLookups`
/// — the model artifact, the free public name, the stored parent and the
/// pinned `Eq` basis.
pub fn check_proj_lookups_model(
    st: &mut AState,
    fe2: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    i: u64,
    cvj: IConstantVal,
) -> Result<(IConstantVal, IConstantVal), CheckError> {
    match core::proj_model_name(st, t, i) {
        Err(e) => Err(e),
        Ok(pmn) => {
            let found: Option<IConstantInfo> = match env::ifenv_find(fe2, &pmn) {
                Some(ci) => Some(env::i_constant_info_dup(ci)),
                None => None,
            };
            match found {
                Some(IConstantInfo::DefnInfo(mcv, _, _)) => {
                    if !core::nidx_vec_beq(&mcv.level_params, lps) {
                        fail(core_types::not_implemented(code_points(&M_PL_MLPS)))
                    } else {
                        match env::proj_fn_name(&mut st.store, t, i) {
                            Err(e) => Err(e),
                            Ok(pn) => {
                                if env::ifenv_find(fe2, &pn).is_some() {
                                    fail(core_types::invalid(code_points(&M_PL_TAKEN)))
                                } else if env::ifenv_find(fe2, t).is_none() {
                                    fail(core_types::not_implemented(code_points(&M_PL_PARENT)))
                                } else {
                                    match eq_basis_stored(st, fe2) {
                                        Err(e) => Err(e),
                                        Ok(false) => {
                                            fail(core_types::not_implemented(code_points(&M_PL_EQ)))
                                        }
                                        Ok(true) => Ok((cvj, mcv)),
                                    }
                                }
                            }
                        }
                    }
                }
                _ => fail(core_types::not_implemented(code_points(&M_PL_MODEL))),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:497-511 checkProjTy
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:522-537 checkProjTy`
/// — stage 2: the public projection type — the model's, renamed back (pinned
/// by the renaming roundtrip), well-formed and parameter-led.  **All three
/// conjuncts of the well-formedness test run**, as the twin's `do` does.
pub fn check_proj_ty(
    st: &mut AState,
    fe2: &IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    mty: &EIdx,
    n_p: u64,
    n_f: u64,
) -> Result<EIdx, CheckError> {
    match proj_back(st, t, ctor_name, n_f) {
        Err(e) => Err(e),
        Ok(back) => match proj_fwd(st, t, ctor_name, n_f) {
            Err(e) => Err(e),
            Ok(fwd) => match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, &back, mty) {
                Err(e) => Err(e),
                Ok(pty) => match expr_ops::rename_consts_fast(st, CORE_WALK_FUEL, &fwd, &pty) {
                    Err(e) => Err(e),
                    Ok(round) => {
                        if !round.eq2(mty) {
                            fail(core_types::not_implemented(code_points(&M_PT_ROUND)))
                        } else {
                            check_proj_ty_wf(st, fe2, lps, n_p, pty)
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:497-511 checkProjTy
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:529-537 checkProjTy`
/// — the public type's resolution, well-formedness and parameter telescope.
pub fn check_proj_ty_wf(
    st: &mut AState,
    fe2: &IFEnv,
    lps: &Vec<NIdx>,
    n_p: u64,
    pty: EIdx,
) -> Result<EIdx, CheckError> {
    match ind_base::consts_resolve_f_fast(st, fe2, &pty) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::not_implemented(code_points(&M_PT_RES))),
        Ok(true) => match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, &pty) {
            Err(e) => Err(e),
            Ok(w1) => match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, &pty) {
                Err(e) => Err(e),
                Ok(w2) => match ind_base::all_level_params_defined(st, lps, &pty) {
                    Err(e) => Err(e),
                    Ok(w3) => {
                        if !(w1 && !w2 && w3) {
                            fail(core_types::not_implemented(code_points(&M_PT_WF)))
                        } else {
                            match expr_ops::strip_pis(st, n_p + 1, &pty) {
                                Err(e) => Err(e),
                                Ok(None) => {
                                    fail(core_types::not_implemented(code_points(&M_PT_TELE)))
                                }
                                Ok(Some(_)) => Ok(pty),
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:541-582 checkProjIota`
/// — stage 4: the model's `proj_i.iota` theorem pins the rule.
pub fn check_proj_iota(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    fe_self: &IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> Result<(), CheckError> {
    const IOTA: [u32; 4] = [105, 111, 116, 97];
    match core::proj_model_name(st, t, i) {
        Err(e) => Err(e),
        Ok(pmn) => match intern_n_node(st, NNodeView::Str(pmn.dup2(), code_points(&IOTA))) {
            Err(e) => Err(e),
            Ok(itn) => {
                let found: Option<IConstantInfo> = match env::ifenv_find(fe2, &itn) {
                    Some(ci) => Some(env::i_constant_info_dup(ci)),
                    None => None,
                };
                match found {
                    Some(IConstantInfo::ThmInfo(tcv, _)) => {
                        if !core::nidx_vec_beq(&tcv.level_params, lps) {
                            fail(core_types::not_implemented(code_points(&M_PI_LPS)))
                        } else {
                            check_proj_iota_doms(
                                st, mode, fe_self, t, ctor_name, lps, cvj, n_p, n_f, i, &pmn,
                                &tcv.ty,
                            )
                        }
                    }
                    _ => fail(core_types::not_implemented(code_points(&M_PI_MISS))),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:549-555 checkProjIota`
/// — the statement's binder domains against the constructor's, under the
/// forward renaming.
pub fn check_proj_iota_doms(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    i: u64,
    pmn: &NIdx,
    tty: &EIdx,
) -> Result<(), CheckError> {
    match expr_ops::strip_pis(st, n_p + n_f, tty) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_PI_TELE))),
        Ok(Some(sq)) => match expr_ops::strip_pis(st, n_p + n_f, &cvj.ty) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::not_implemented(code_points(&M_PI_CTELE))),
            Ok(Some(cq)) => match proj_fwd(st, t, ctor_name, n_f) {
                Err(e) => Err(e),
                Ok(fwd) => match doms_match_renamed(st, &fwd, &sq.0, &cq.0, 0, 0, n_p + n_f) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::not_implemented(code_points(&M_PI_DOM))),
                    Ok(true) => check_proj_iota_body(
                        st, mode, fe_self, ctor_name, lps, cvj, n_p, n_f, i, pmn, tty, &sq.1,
                    ),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:556-582 checkProjIota`
/// — the statement's body is `proj_i p⃗ (C._model p⃗ x⃗) = x_i`, and then both
/// equation sides are certified against the statement's type slot.
pub fn check_proj_iota_body(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    i: u64,
    pmn: &NIdx,
    tty: &EIdx,
    sbody: &EIdx,
) -> Result<(), CheckError> {
    match struct_parts::struct_ps_at(st, n_f, n_p) {
        Err(e) => Err(e),
        Ok(p_args) => match struct_parts::bvars_desc(st, n_f) {
            Err(e) => Err(e),
            Ok(x_args) => match ind_base::model_name(st, ctor_name) {
                Err(e) => Err(e),
                Ok(cmn) => match struct_parts::param_levels(st, &cvj.level_params) {
                    Err(e) => Err(e),
                    Ok(cus) => match intern_e(st, ENodeView::Const(cmn, cus)) {
                        Err(e) => Err(e),
                        Ok(c_hd) => {
                            let spine: Vec<EIdx> =
                                core::append_eidx(env::eidx_vec_dup(&p_args), &x_args);
                            match expr_ops::mk_app_n(st, &c_hd, &spine) {
                                Err(e) => Err(e),
                                Ok(mk_spine) => check_proj_iota_lhs(
                                    st, mode, fe_self, lps, n_p, n_f, i, pmn, tty, sbody, &p_args,
                                    &mk_spine,
                                ),
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:563-575 checkProjIota`
/// — the expected redex, and the three pins the statement's body must meet.
pub fn check_proj_iota_lhs(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    i: u64,
    pmn: &NIdx,
    tty: &EIdx,
    sbody: &EIdx,
    p_args: &Vec<EIdx>,
    mk_spine: &EIdx,
) -> Result<(), CheckError> {
    match struct_parts::param_levels(st, lps) {
        Err(e) => Err(e),
        Ok(pus) => match intern_e(st, ENodeView::Const(pmn.dup2(), pus)) {
            Err(e) => Err(e),
            Ok(p_hd) => {
                let args: Vec<EIdx> = core::snoc_eidx(env::eidx_vec_dup(p_args), mk_spine);
                match expr_ops::mk_app_n(st, &p_hd, &args) {
                    Err(e) => Err(e),
                    Ok(lhs_s) => match eq_app3(st, sbody) {
                        Err(e) => Err(e),
                        Ok(None) => fail(core_types::not_implemented(code_points(&M_PI_SHAPE))),
                        Ok(Some(q)) => match core::pin(st, &basis_names::eq_name()) {
                            Err(e) => Err(e),
                            Ok(en) => {
                                if !q.0.eq2(&en) {
                                    fail(core_types::not_implemented(code_points(&M_PI_HEAD)))
                                } else if !q.3.eq2(&lhs_s) {
                                    fail(core_types::not_implemented(code_points(&M_PI_REDEX)))
                                } else {
                                    check_proj_iota_field(
                                        st, mode, fe_self, n_p, n_f, i, tty, sbody, &q.4,
                                    )
                                }
                            }
                        },
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:513-563 checkProjIota
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:572-582 checkProjIota`
/// — the right side is field `i`, and both equation sides inhabit the
/// statement's type slot (the telescope opened at free variables).
pub fn check_proj_iota_field(
    st: &mut AState,
    mode: &CheckMode,
    fe_self: &IFEnv,
    n_p: u64,
    n_f: u64,
    i: u64,
    tty: &EIdx,
    sbody: &EIdx,
    rhs_c: &EIdx,
) -> Result<(), CheckError> {
    let depth: u64 = n_p + n_f;
    match intern_e(st, ENodeView::BVar(sub_nat(sub_nat(n_f, 1), i))) {
        Err(e) => Err(e),
        Ok(fld) => {
            if !rhs_c.eq2(&fld) {
                fail(core_types::not_implemented(code_points(&M_PI_FIELD)))
            } else {
                match ind_base::open_pis_at_fvars_f(st, depth, tty, 0) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::not_implemented(code_points(&M_PI_TELE))),
                    Ok(Some(oq)) => match expr_ops::get_app_args(st, CORE_WALK_FUEL, &oq.1) {
                        Err(e) => Err(e),
                        Ok(targs_o) => match intern_e(st, ENodeView::BVar(0)) {
                            Err(e) => Err(e),
                            Ok(b0) => match expr_ops::get_app_fn(st, CORE_WALK_FUEL, sbody) {
                                Err(e) => Err(e),
                                Ok(hd) => match ind_base::eq_head_level(st, &hd) {
                                    Err(e) => Err(e),
                                    Ok(l_a) => {
                                        let a0 = core::get_d_eidx(&targs_o, 0, &b0);
                                        let a1 = core::get_d_eidx(&targs_o, 1, &b0);
                                        let a2 = core::get_d_eidx(&targs_o, 2, &b0);
                                        check_iota_sides_ty(
                                            st, mode, fe_self, depth, &a0, &a1, &a2, &l_a,
                                        )
                                    }
                                },
                            },
                        },
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:565-584 checkProjFn
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:588-599 checkProjFn`
/// — check and install the public projection function for field `i` of a
/// modeled single-constructor structure.  The function is stored as a
/// degenerate recursor (no motive, no minors) carrying one rule.
pub fn check_proj_fn(
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> Result<IFEnv, CheckError> {
    match check_proj_lookups(st, &fe2, t, ctor_name, lps, n_p, n_f, i) {
        Err(e) => Err(e),
        Ok(q) => {
            let cvj: IConstantVal = q.0;
            let mcv: IConstantVal = q.1;
            match check_proj_ty(st, &fe2, t, ctor_name, lps, &mcv.ty, n_p, n_f) {
                Err(e) => Err(e),
                Ok(pty) => match ind_base::check_proj_shape(st, &pty, &cvj.ty, n_p, n_f) {
                    Err(e) => Err(e),
                    Ok(()) => {
                        if i >= n_f {
                            fail(core_types::invalid(code_points(&M_PROJ_RANGE)))
                        } else {
                            check_proj_fn_rule(
                                st, mode, fe2, t, ctor_name, lps, &cvj, n_p, n_f, i, pty,
                            )
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:565-584 checkProjFn
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:595-599 checkProjFn`
/// — the rule, the model's iota theorem, and the install.
pub fn check_proj_fn_rule(
    st: &mut AState,
    mode: &CheckMode,
    fe2: IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    i: u64,
    pty: EIdx,
) -> Result<IFEnv, CheckError> {
    match ind_base::check_proj_rule(st, mode, &fe2, &pty, cvj, lps, n_p, n_f, i) {
        Err(e) => Err(e),
        Ok(rhs_a) => {
            match check_proj_iota(st, mode, &fe2, &fe2, t, ctor_name, lps, cvj, n_p, n_f, i) {
                Err(e) => Err(e),
                Ok(()) => match env::proj_fn_name(&mut st.store, t, i) {
                    Err(e) => Err(e),
                    Ok(pn) => {
                        match core::proj_fn_rule(st, &fe2, t, ctor_name, &pty, n_p, n_f, i, &rhs_a)
                        {
                            Err(e) => Err(e),
                            Ok(rule) => {
                                let cv = IConstantVal {
                                    name: pn,
                                    level_params: env::nidx_vec_dup(lps),
                                    ty: pty,
                                };
                                let mut rules: Vec<IRecRule> = Vec::new();
                                rules.push(rule);
                                Ok(env::ifenv_push(
                                    fe2,
                                    IConstantInfo::RecInfo(cv, n_p, n_p, rules),
                                ))
                            }
                        }
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The capabilities (`Modeled.lean:601-745` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:606-648 checkEtaThm`
/// — does the model document structural eta for this single-constructor block
/// — a `T._model.eta` theorem with the pinned statement?
pub fn check_eta_thm(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
) -> Result<bool, CheckError> {
    const ETA: [u32; 3] = [101, 116, 97];
    match ind_base::model_name(st, t) {
        Err(e) => Err(e),
        Ok(tm) => match intern_n_node(st, NNodeView::Str(tm.dup2(), code_points(&ETA))) {
            Err(e) => Err(e),
            Ok(etn) => match ind_base::model_name(st, ctor_name) {
                Err(e) => Err(e),
                Ok(cm) => {
                    let a = match env::ifenv_find(fe2, &etn) {
                        Some(ci) => Some(env::i_constant_info_dup(ci)),
                        None => None,
                    };
                    let b = match env::ifenv_find(fe2, &tm) {
                        Some(ci) => Some(env::i_constant_info_dup(ci)),
                        None => None,
                    };
                    let c = match env::ifenv_find(fe2, &cm) {
                        Some(ci) => Some(env::i_constant_info_dup(ci)),
                        None => None,
                    };
                    match (a, b, c) {
                        (
                            Some(IConstantInfo::ThmInfo(tcv, _)),
                            Some(IConstantInfo::DefnInfo(cvm_t, _, _)),
                            Some(IConstantInfo::DefnInfo(cvm_c, _, _)),
                        ) => check_eta_thm_at(
                            st, mode, fe2, t, lps, n_p, n_f, &tm, &cm, &tcv, &cvm_t, &cvm_c,
                        ),
                        _ => Ok(false),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:613-621 checkEtaThm`
/// — the pinned `Eq` basis, the three level-parameter pins and the projection
/// models' own level parameters.
pub fn check_eta_thm_at(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    tm: &NIdx,
    cm: &NIdx,
    tcv: &IConstantVal,
    cvm_t: &IConstantVal,
    cvm_c: &IConstantVal,
) -> Result<bool, CheckError> {
    match eq_basis_stored(st, fe2) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => {
            if !(core::nidx_vec_beq(&tcv.level_params, lps)
                && core::nidx_vec_beq(&cvm_t.level_params, lps)
                && core::nidx_vec_beq(&cvm_c.level_params, lps))
            {
                Ok(false)
            } else {
                match proj_models_ok(st, fe2, t, lps, n_f, 0) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => {
                        check_eta_thm_shape(st, mode, t, lps, n_p, n_f, tm, cm, &tcv.ty, &cvm_t.ty)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:617-620 checkEtaThm`
/// — the projection models exist at the family's level parameters.
pub fn proj_models_ok(
    st: &mut AState,
    fe2: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_f: u64,
    j: u64,
) -> Result<bool, CheckError> {
    if j >= n_f {
        Ok(true)
    } else {
        match core::proj_model_name(st, t, j) {
            Err(e) => Err(e),
            Ok(pmn) => {
                let found: Option<IConstantInfo> = match env::ifenv_find(fe2, &pmn) {
                    Some(ci) => Some(env::i_constant_info_dup(ci)),
                    None => None,
                };
                match found {
                    Some(IConstantInfo::DefnInfo(cvmj, _, _)) => {
                        if core::nidx_vec_beq(&cvmj.level_params, lps) {
                            proj_models_ok(st, fe2, t, lps, n_f, j + 1)
                        } else {
                            Ok(false)
                        }
                    }
                    _ => Ok(false),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:622-647 checkEtaThm`
/// — the statement's shape: the parameter domains are the model former's, the
/// subject's domain is the model family, and the body is
/// `x = C._model p⃗ (proj_0 p⃗ x) … (proj_{n-1} p⃗ x)` at the family's type.
pub fn check_eta_thm_shape(
    st: &mut AState,
    mode: &CheckMode,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    tm: &NIdx,
    cm: &NIdx,
    tty: &EIdx,
    mtty: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::strip_pis(st, n_p + 1, tty) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(sq)) => match expr_ops::strip_pis(st, n_p, mtty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(tq)) => {
                if !ind_base::doms_match_aux(&sq.0, &tq.0, 0, 0, n_p) {
                    Ok(false)
                } else {
                    match struct_parts::param_levels(st, lps) {
                        Err(e) => Err(e),
                        Ok(us) => match intern_e(st, ENodeView::Const(tm.dup2(), us)) {
                            Err(e) => Err(e),
                            Ok(t_hd) => check_eta_thm_body(
                                st, mode, t, lps, n_p, n_f, &t_hd, cm, &sq.0, &sq.1, &tq.1,
                            ),
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:627-647 checkEtaThm`
/// — the subject binder's domain and the equation body.
pub fn check_eta_thm_body(
    st: &mut AState,
    mode: &CheckMode,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    t_hd: &EIdx,
    cm: &NIdx,
    sbinders: &Vec<(EIdx, BinderMeta)>,
    sbody: &EIdx,
    tbody_m: &EIdx,
) -> Result<bool, CheckError> {
    match struct_parts::struct_ps_at(st, 0, n_p) {
        Err(e) => Err(e),
        Ok(ps_lo) => match expr_ops::mk_app_n(st, t_hd, &ps_lo) {
            Err(e) => Err(e),
            Ok(fam_lo) => {
                let xdom_ok: bool = if (n_p as usize) < sbinders.len() {
                    sbinders[n_p as usize].0.eq2(&fam_lo)
                } else {
                    false
                };
                if !xdom_ok {
                    Ok(false)
                } else {
                    match struct_parts::struct_ps_at(st, 1, n_p) {
                        Err(e) => Err(e),
                        Ok(ps_hi) => match expr_ops::mk_app_n(st, t_hd, &ps_hi) {
                            Err(e) => Err(e),
                            Ok(fam_hi) => check_eta_thm_eq(
                                st, mode, t, lps, n_f, cm, sbody, tbody_m, &ps_hi, &fam_hi,
                            ),
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:635-646 checkEtaThm`
/// — the equation itself: `x = C._model p⃗ (proj_j p⃗ x)…`, at the family's
/// type, with the TT-lane check that the model former's residual is `Sort ℓA`.
pub fn check_eta_thm_eq(
    st: &mut AState,
    mode: &CheckMode,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_f: u64,
    cm: &NIdx,
    sbody: &EIdx,
    tbody_m: &EIdx,
    ps_hi: &Vec<EIdx>,
    fam_hi: &EIdx,
) -> Result<bool, CheckError> {
    match eq_app3(st, sbody) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(q)) => match intern_e(st, ENodeView::BVar(0)) {
            Err(e) => Err(e),
            Ok(b0) => match struct_parts::param_levels(st, lps) {
                Err(e) => Err(e),
                Ok(us) => match intern_e(st, ENodeView::Const(cm.dup2(), us)) {
                    Err(e) => Err(e),
                    Ok(c_hd) => match eta_proj_args(st, t, lps, ps_hi, &b0, n_f, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(proj_args) => {
                            let spine: Vec<EIdx> =
                                core::append_eidx(env::eidx_vec_dup(ps_hi), &proj_args);
                            match expr_ops::mk_app_n(st, &c_hd, &spine) {
                                Err(e) => Err(e),
                                Ok(want_rhs) => match intern_e(st, ENodeView::Sort(q.1.dup2())) {
                                    Err(e) => Err(e),
                                    Ok(sort_a) => match core::pin(st, &basis_names::eq_name()) {
                                        Err(e) => Err(e),
                                        Ok(en) => Ok(q.0.eq2(&en)
                                            && q.3.eq2(&b0)
                                            && q.2.eq2(fam_hi)
                                            && q.4.eq2(&want_rhs)
                                            && (!con_ron_core::kernel::env::tt_checks(mode)
                                                || tbody_m.eq2(&sort_a))),
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

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:586-642 checkEtaThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:639-641 checkEtaThm`
/// — the cursor recursion the `(List.range nF).mapM` becomes: `proj_j._model`
/// at the parameter spine and the subject.
pub fn eta_proj_args(
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    ps_hi: &Vec<EIdx>,
    b0: &EIdx,
    n_f: u64,
    j: u64,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if j >= n_f {
        Ok(out)
    } else {
        match core::proj_model_name(st, t, j) {
            Err(e) => Err(e),
            Ok(pmn) => match struct_parts::param_levels(st, lps) {
                Err(e) => Err(e),
                Ok(us) => match intern_e(st, ENodeView::Const(pmn, us)) {
                    Err(e) => Err(e),
                    Ok(p_hd) => {
                        let args: Vec<EIdx> = core::snoc_eidx(env::eidx_vec_dup(ps_hi), b0);
                        match expr_ops::mk_app_n(st, &p_hd, &args) {
                            Err(e) => Err(e),
                            Ok(a) => {
                                let mut o: Vec<EIdx> = out;
                                o.push(a);
                                eta_proj_args(st, t, lps, ps_hi, b0, n_f, j + 1, o)
                            }
                        }
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:653-685 checkUnitThm`
/// — does the model document unit-likeness for this block — a
/// `T._model.unitlike` theorem with the pinned statement
/// `∀ p⃗ (x y : T._model p⃗), x = y`?
pub fn check_unit_thm(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
) -> Result<bool, CheckError> {
    const UL: [u32; 8] = [117, 110, 105, 116, 108, 105, 107, 101];
    match ind_base::model_name(st, t) {
        Err(e) => Err(e),
        Ok(tm) => match intern_n_node(st, NNodeView::Str(tm.dup2(), code_points(&UL))) {
            Err(e) => Err(e),
            Ok(utn) => {
                let a = match env::ifenv_find(fe2, &utn) {
                    Some(ci) => Some(env::i_constant_info_dup(ci)),
                    None => None,
                };
                let b = match env::ifenv_find(fe2, &tm) {
                    Some(ci) => Some(env::i_constant_info_dup(ci)),
                    None => None,
                };
                match (a, b) {
                    (
                        Some(IConstantInfo::ThmInfo(tcv, _)),
                        Some(IConstantInfo::DefnInfo(cvm_t, _, _)),
                    ) => check_unit_thm_at(
                        st,
                        mode,
                        fe2,
                        lps,
                        n_p,
                        &tm,
                        &tcv.ty,
                        &tcv.level_params,
                        &cvm_t.ty,
                        &cvm_t.level_params,
                    ),
                    _ => Ok(false),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:659-685 checkUnitThm`
/// — the pinned `Eq` basis, the level-parameter pins and the statement's
/// shape.
pub fn check_unit_thm_at(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    lps: &Vec<NIdx>,
    n_p: u64,
    tm: &NIdx,
    tty: &EIdx,
    tlps: &Vec<NIdx>,
    mtty: &EIdx,
    mlps: &Vec<NIdx>,
) -> Result<bool, CheckError> {
    match eq_basis_stored(st, fe2) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => {
            if !(core::nidx_vec_beq(tlps, lps) && core::nidx_vec_beq(mlps, lps)) {
                Ok(false)
            } else {
                match expr_ops::strip_pis(st, n_p + 2, tty) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(false),
                    Ok(Some(sq)) => match expr_ops::strip_pis(st, n_p, mtty) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(false),
                        Ok(Some(tq)) => {
                            if !ind_base::doms_match_aux(&sq.0, &tq.0, 0, 0, n_p) {
                                Ok(false)
                            } else {
                                check_unit_thm_shape(st, mode, lps, n_p, tm, &sq.0, &sq.1, &tq.1)
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:664-685 checkUnitThm`
/// — the two subject binders' domains and the equation `x = y` at the
/// family's type.
pub fn check_unit_thm_shape(
    st: &mut AState,
    mode: &CheckMode,
    lps: &Vec<NIdx>,
    n_p: u64,
    tm: &NIdx,
    sbinders: &Vec<(EIdx, BinderMeta)>,
    sbody: &EIdx,
    tbody_m: &EIdx,
) -> Result<bool, CheckError> {
    match struct_parts::param_levels(st, lps) {
        Err(e) => Err(e),
        Ok(us) => match intern_e(st, ENodeView::Const(tm.dup2(), us)) {
            Err(e) => Err(e),
            Ok(t_hd) => match fam_at(st, &t_hd, 0, n_p) {
                Err(e) => Err(e),
                Ok(fam0) => match fam_at(st, &t_hd, 1, n_p) {
                    Err(e) => Err(e),
                    Ok(fam1) => match fam_at(st, &t_hd, 2, n_p) {
                        Err(e) => Err(e),
                        Ok(fam2) => {
                            let x_ok: bool = if (n_p as usize) < sbinders.len() {
                                sbinders[n_p as usize].0.eq2(&fam0)
                            } else {
                                false
                            };
                            let y_ok: bool = if ((n_p + 1) as usize) < sbinders.len() {
                                sbinders[(n_p + 1) as usize].0.eq2(&fam1)
                            } else {
                                false
                            };
                            if !(x_ok && y_ok) {
                                Ok(false)
                            } else {
                                check_unit_thm_eq(st, mode, sbody, tbody_m, &fam2)
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: none — `mkAppN tHd (← structPsAt o nP)`, the model family at an offset
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:666-668 checkUnitThm`
/// — the twin writes the same expression at three offsets.
pub fn fam_at(st: &mut AState, t_hd: &EIdx, o: u64, n_p: u64) -> Result<EIdx, CheckError> {
    match struct_parts::struct_ps_at(st, o, n_p) {
        Err(e) => Err(e),
        Ok(ps) => expr_ops::mk_app_n(st, t_hd, &ps),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:644-680 checkUnitThm
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:676-683 checkUnitThm`
/// — the equation `bvar 1 = bvar 0` at the family's type.
pub fn check_unit_thm_eq(
    st: &mut AState,
    mode: &CheckMode,
    sbody: &EIdx,
    tbody_m: &EIdx,
    fam2: &EIdx,
) -> Result<bool, CheckError> {
    match eq_app3(st, sbody) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(q)) => match intern_e(st, ENodeView::BVar(0)) {
            Err(e) => Err(e),
            Ok(b0) => match intern_e(st, ENodeView::BVar(1)) {
                Err(e) => Err(e),
                Ok(b1) => match intern_e(st, ENodeView::Sort(q.1.dup2())) {
                    Err(e) => Err(e),
                    Ok(sort_a) => match core::pin(st, &basis_names::eq_name()) {
                        Err(e) => Err(e),
                        Ok(en) => Ok(q.0.eq2(&en)
                            && q.3.eq2(&b1)
                            && q.4.eq2(&b0)
                            && q.2.eq2(fam2)
                            && (!con_ron_core::kernel::env::tt_checks(mode)
                                || tbody_m.eq2(&sort_a))),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:682-710 ctorTargetsFam
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:691-697 ctorTargetsFam`
/// — **official's structure-likeness, read off the block's own constructor**:
/// one constructor and no indices, i.e. the constructor targets the family at
/// exactly its parameters.
pub fn ctor_targets_fam(
    st: &mut AState,
    ctor_ty: &EIdx,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
) -> Result<bool, CheckError> {
    match expr_ops::strip_pis(st, n_p + n_f, ctor_ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(q)) => match struct_parts::struct_fam(st, t, lps, n_p, n_f) {
            Err(e) => Err(e),
            Ok(fam) => Ok(q.1.eq2(&fam)),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:712-722 installProjFnStep
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:702-706 installProjFnStep`
/// — one projection-function install step (skipped where the model's
/// projection artifact is absent).
pub fn install_proj_fn_step(
    st: &mut AState,
    mode: &CheckMode,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    e: IFEnv,
    i: u64,
) -> Result<IFEnv, CheckError> {
    match core::proj_model_name(st, t, i) {
        Err(er) => Err(er),
        Ok(pmn) => {
            if env::ifenv_find(&e, &pmn).is_some() {
                check_proj_fn(st, mode, e, t, ctor_name, lps, n_p, n_f, i)
            } else {
                Ok(e)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:710-715 installProjFns`
/// — the projection fold, as an explicit recursion.
pub fn install_proj_fns(
    st: &mut AState,
    mode: &CheckMode,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    fe: IFEnv,
    k: u64,
    i: u64,
) -> Result<IFEnv, CheckError> {
    if k == 0 {
        Ok(fe)
    } else {
        match install_proj_fn_step(st, mode, t, ctor_name, lps, n_p, n_f, fe, i) {
            Err(e) => Err(e),
            Ok(fe2) => install_proj_fns(st, mode, t, ctor_name, lps, n_p, n_f, fe2, k - 1, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:724-735 indBlockCaps
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:719-730 indBlockCaps`
/// — the capabilities recorded for a single-constructor modeled block.
/// **`checkEtaThm` runs whatever the level-parameter test says**: Lean lifts
/// the `(← …)` out of the `&&`, so a short-circuiting Rust would leave the
/// store several names behind the twin's.
pub fn ind_block_caps(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv_t: &IConstantVal,
    cv_c: &IConstantVal,
    n_p: u64,
    n_f: u64,
) -> Result<IIndCaps, CheckError> {
    let lps_eq: bool = core::nidx_vec_beq(&cv_c.level_params, &cv_t.level_params);
    match check_eta_thm(
        st,
        mode,
        fe,
        &cv_t.name,
        &cv_c.name,
        &cv_t.level_params,
        n_p,
        n_f,
    ) {
        Err(e) => Err(e),
        Ok(thm) => {
            let eta: bool = lps_eq && thm;
            match check_unit_thm(st, mode, fe, &cv_t.name, &cv_t.level_params, n_p) {
                Err(e) => Err(e),
                Ok(unitlike) => match core::pi_result_is_prop(st, &cv_t.ty) {
                    Err(e) => Err(e),
                    Ok(pr) => match core::pi_result_z(st, &cv_t.ty) {
                        Err(e) => Err(e),
                        Ok(sort_z) => Ok(IIndCaps {
                            eta,
                            eta_ctor: cv_c.name.dup2(),
                            eta_params: n_p,
                            eta_fields: n_f,
                            unitlike,
                            unit_params: n_p,
                            rule_k: n_f == 0 && pr,
                            sort_z,
                        }),
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:744-779 ctorResidualOk
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:735-745 ctorResidualOk`
/// — **con-leche's task #136: an eta-capable family's constructor returns the
/// family applied to its parameters.**  The subject is the STORED constant.
pub fn ctor_residual_ok(
    st: &mut AState,
    mode: &CheckMode,
    fe2: &IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    eta: bool,
) -> Result<bool, CheckError> {
    if !con_ron_core::kernel::env::tt_checks(mode) || !eta {
        Ok(true)
    } else {
        let found: Option<IConstantInfo> = match env::ifenv_find(fe2, ctor_name) {
            Some(ci) => Some(env::i_constant_info_dup(ci)),
            None => None,
        };
        match found {
            Some(IConstantInfo::CtorInfo(cv_ca, _, _)) => {
                match expr_ops::strip_pis(st, n_p + n_f, &cv_ca.ty) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(false),
                    Ok(Some(q)) => match struct_parts::struct_fam(st, t, lps, n_p, n_f) {
                        Err(e) => Err(e),
                        Ok(fam) => Ok(q.1.eq2(&fam)),
                    },
                }
            }
            _ => Ok(false),
        }
    }
}

// ---------------------------------------------------------------------------
// The install (`Modeled.lean:747-783` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — `block.filter ConstantInfo.isRecInfo` (and its complement)
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:756-757 checkModeled`
/// — the two filters the install opens with, as one cursor recursion.
pub fn filter_recs(
    block: &Vec<IConstantInfo>,
    want: bool,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Vec<IConstantInfo> {
    if i >= block.len() {
        out
    } else if ind_base::is_rec_info(&block[i]) == want {
        let mut o: Vec<IConstantInfo> = out;
        o.push(env::i_constant_info_dup(&block[i]));
        filter_recs(block, want, i + 1, o)
    } else {
        filter_recs(block, want, i + 1, out)
    }
}

/// con-leche: none — `block.map ConstantInfo.name`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:761 checkModeled` —
/// the block's names, as one cursor recursion.
pub fn block_names_of(block: &Vec<IConstantInfo>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= block.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(env::i_constant_info_name(&block[i]));
        block_names_of(block, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:762-764 checkModeled`
/// — the twin matches the two filtered lists against `[.indInfo cvT _]` and
/// `[.ctorInfo cvC nP nF]`; here that is one reader, so the arm's binder names
/// come out as a record rather than as a nested pattern.
pub fn single_ind_ctor(
    block: &Vec<IConstantInfo>,
) -> Option<(IConstantVal, IConstantVal, u64, u64)> {
    let inds: Vec<IConstantInfo> = filter_kind(block, 0, 0, Vec::new());
    let ctors: Vec<IConstantInfo> = filter_kind(block, 1, 0, Vec::new());
    if inds.len() != 1 || ctors.len() != 1 {
        None
    } else {
        match (&inds[0], &ctors[0]) {
            (IConstantInfo::IndInfo(cv_t, _), IConstantInfo::CtorInfo(cv_c, n_p, n_f)) => Some((
                env::i_constant_val_dup(cv_t),
                env::i_constant_val_dup(cv_c),
                *n_p,
                *n_f,
            )),
            _ => None,
        }
    }
}

/// con-leche: none — `block.filter (fun ci => ci matches .indInfo …)`
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:762-763 checkModeled`
/// — the two constructor filters, at a tag (`0` the type formers, `1` the
/// constructors).
pub fn filter_kind(
    block: &Vec<IConstantInfo>,
    kind: u64,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Vec<IConstantInfo> {
    if i >= block.len() {
        out
    } else {
        let hit: bool = match &block[i] {
            IConstantInfo::IndInfo(_, _) => kind == 0,
            IConstantInfo::CtorInfo(_, _, _) => kind == 1,
            _ => false,
        };
        if hit {
            let mut o: Vec<IConstantInfo> = out;
            o.push(env::i_constant_info_dup(&block[i]));
            filter_kind(block, kind, i + 1, o)
        } else {
            filter_kind(block, kind, i + 1, out)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:752-781 checkModeled`
/// — check and install a modeled inductive block: every member is checked
/// against its `_model` counterpart, then stored as a real inductive-kind
/// constant.
pub fn check_modeled(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
) -> Result<IFEnv, CheckError> {
    let recs: Vec<IConstantInfo> = filter_recs(block, true, 0, Vec::new());
    let nonrecs: Vec<IConstantInfo> = filter_recs(block, false, 0, Vec::new());
    if !ind_base::recs_form_suffix(block) {
        fail(core_types::not_implemented(code_points(&M_ORDER_BLOCK)))
    } else {
        let block_names: Vec<NIdx> = block_names_of(block, 0, Vec::new());
        match single_ind_ctor(block) {
            Some(sq) => check_modeled_struct(
                st,
                mode,
                fe,
                &block_names,
                &nonrecs,
                &recs,
                &sq.0,
                &sq.1,
                sq.2,
                sq.3,
            ),
            None => {
                let caps: IIndCaps = env::i_ind_caps_default();
                match check_ind_members(st, mode, &block_names, &caps, fe, &nonrecs, 0) {
                    Err(e) => Err(e),
                    Ok(fe2) => check_ind_recs(st, mode, &block_names, fe2, &recs),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:764-778 checkModeled`
/// — the single-type-former, single-constructor arm: the capability record,
/// the members, the recursors, the eta constructor residual, the projection
/// name family's freshness and — at a structure-like block — the projection
/// functions.
pub fn check_modeled_struct(
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block_names: &Vec<NIdx>,
    nonrecs: &Vec<IConstantInfo>,
    recs: &Vec<IConstantInfo>,
    cv_t: &IConstantVal,
    cv_c: &IConstantVal,
    n_p: u64,
    n_f: u64,
) -> Result<IFEnv, CheckError> {
    match ind_block_caps(st, mode, &fe, cv_t, cv_c, n_p, n_f) {
        Err(e) => Err(e),
        Ok(caps) => {
            let eta: bool = caps.eta;
            match check_ind_members(st, mode, block_names, &caps, fe, nonrecs, 0) {
                Err(e) => Err(e),
                Ok(fe2) => match check_ind_recs(st, mode, block_names, fe2, recs) {
                    Err(e) => Err(e),
                    Ok(fe3) => check_modeled_projs(st, mode, fe3, cv_t, cv_c, n_p, n_f, eta),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:768-778 checkModeled`
/// — the eta constructor residual, the projection name family's freshness and
/// the projection installs.
pub fn check_modeled_projs(
    st: &mut AState,
    mode: &CheckMode,
    fe3: IFEnv,
    cv_t: &IConstantVal,
    cv_c: &IConstantVal,
    n_p: u64,
    n_f: u64,
    eta: bool,
) -> Result<IFEnv, CheckError> {
    match ctor_residual_ok(
        st,
        mode,
        &fe3,
        &cv_t.name,
        &cv_c.name,
        &cv_t.level_params,
        n_p,
        n_f,
        eta,
    ) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::not_implemented(code_points(&M_ETA_RESID))),
        Ok(true) => match proj_fn_family_free(st, &fe3, &cv_t.name, n_f, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_FAM_TAKEN))),
            Ok(true) => {
                match ctor_targets_fam(st, &cv_c.ty, &cv_t.name, &cv_t.level_params, n_p, n_f) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(fe3),
                    Ok(true) => install_proj_fns(
                        st,
                        mode,
                        &cv_t.name,
                        &cv_c.name,
                        &cv_t.level_params,
                        n_p,
                        n_f,
                        fe3,
                        n_f,
                        0,
                    ),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:772-774 checkModeled`
/// — is the whole projection-function name family free?  The same test the
/// direct route's table install makes (`checkStructProjTable`), as one cursor
/// recursion.
pub fn proj_fn_family_free(
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n_f: u64,
    j: u64,
) -> Result<bool, CheckError> {
    if j >= n_f {
        Ok(true)
    } else {
        match env::proj_fn_name(&mut st.store, t, j) {
            Err(e) => Err(e),
            Ok(pn) => {
                if env::ifenv_find(fe, &pn).is_none() {
                    proj_fn_family_free(st, fe, t, n_f, j + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}
