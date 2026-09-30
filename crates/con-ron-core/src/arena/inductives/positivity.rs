//! `arena::inductives::positivity` — positivity through containers.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/Positivity.lean`, which is
//! `ConLeche/Kernel/Inductives/Positivity.lean` over handles: the occurrence
//! tests, the whole-application abstraction of a frame's group to its holes,
//! the readback of a walked term, and the ONE positivity function `nestPos`
//! with its container case (`nestCont`, `nestContKey`, `nestContNew`,
//! `nestFrame`), its root frame (`nestRoot`), official's uniform-occurrence
//! check (`nestUniform`) and the seeds (`nestSeeds`).
//!
//! ## The twin's deviations
//!
//! * **A pure walk, its memoised walk and its `Fast` entry are ONE memoised
//!   walk over handles** (`mentionsAnyConst`, `nestOcc`, `replaceFVars`,
//!   `replaceApps`, `Expr.depth`), keyed by the handle, with a fresh memo per
//!   top-level call as con-leche's `…Fast` has; each is a `…_go` walk, a
//!   `…_node` step (so the `view`'s loans die before the memo's join,
//!   extraction rule 5) and an entry.  The `MemoInv`s and `_spec`s are proofs.
//! * **`NestCtx.find?` is the environment and its visibility bound**: the
//!   record carries `vis`, and every function that reads the environment takes
//!   `fe: &IFEnv` beside it — the arena has one environment representation,
//!   and a `find?` field is a closure.  The record also carries `lvls`, the
//!   block's own level parameters as levels (`ctx.lps.map .param`), interned
//!   once: over handles `List Level` equality is the interned list's handle.
//! * **`replaceFVars`' function argument is the enum `FvMap`**, one variant
//!   per instantiation con-leche writes (`nestHoleImg ctx prog`, `nestKeyMap
//!   ds holes`, `eraseFVarTys`' constant map, `targetCanonParams`' opener
//!   lookup), dispatched by `fv_map_at` — §3.4 forbids the closure, and the
//!   maps intern, so a trait would be a `&mut`-taking generic
//!   (`frontend::proj_rec`'s module note).  `replaceApps` has ONE
//!   instantiation (`nestCanonSub`), so it is that walk, specialised.
//! * **The frame stack `prog` is a `Vec` in OUTERMOST-first order** (the
//!   reverse of con-leche's innermost-first list): a frame's group is
//!   appended where con-leche prepends its reversal, `nestHoleAt`'s
//!   `rootHoles ++ prog.reverse` is `root_holes ++ prog`, and `nestHoleImg`'s
//!   `h :: prog` is the vector's prefix of length `n` with `h` its last.
//! * **`nestPos`'s continuation `rec` is the function itself** at an explicit
//!   fuel: every `rec` con-leche passes is `nestPos ops env ctx F` for some
//!   `F` — the enclosing walk's fuel inside a frame, `whnfWalkFuel crest` per
//!   root constructor (`nestRoot`), the seed's fold (`nestSeeds`) — so
//!   `nest_ctors` takes a `root` flag and a fuel.
//! * **A pure term computed twice is computed once**: `closeTelescope nds hi
//!   cur` (U4, the normal-form record and the returned form) and
//!   `ty.piBinders` (`nestInstType`).  Interning is deterministic, so the
//!   second computation would return the same handle and intern nothing.
//! * **`NestedPositivity` and `nestedBlockPositivity` are not ported**: the
//!   unit tests' entry; the install runs `nestUniform`/`nestRoot` itself
//!   (`checkBlockPositivity`).  The skip list says so.

use super::field_tele::pi_binders;
use super::struct_parts;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_APP, ETAG_CONST, ETAG_FORALL_E, ETAG_FVAR};
use crate::arena::monad::{
    fail, fail_dangling_e, intern_e_app, intern_e_const, intern_e_forall_e, intern_e_fvar,
    intern_e_lam, intern_e_let_e, intern_e_proj, intern_e_sort, intern_n_node, view, view_app,
    view_bind, view_const, view_fvar_idx, AState,
};
use crate::arena::pins::pin_quot;
use crate::arena::store::{ENodeView, NNodeView, PersTier};
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased as every arena module does.
use crate::ron::hashmap2::HashMap2 as HashMap;

// ---------------------------------------------------------------------------
// The messages (con-leche's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: mentionsAnyConst`, as code points.
pub const M_FUEL_MENTIONS_ANY: [u32; 32] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 109, 101, 110, 116,
    105, 111, 110, 115, 65, 110, 121, 67, 111, 110, 115, 116,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: nestOcc`, as code points.
pub const M_FUEL_NEST_OCC: [u32; 23] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 110, 101, 115, 116,
    79, 99, 99,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: depth`, as code points.
pub const M_FUEL_DEPTH: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 100, 101, 112, 116,
    104,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: replaceFVars`, as code points.
pub const M_FUEL_REPLACE_FVARS: [u32; 28] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 114, 101, 112, 108,
    97, 99, 101, 70, 86, 97, 114, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: replaceApps`, as code points.
pub const M_FUEL_REPLACE_APPS: [u32; 27] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 114, 101, 112, 108,
    97, 99, 101, 65, 112, 112, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: non valid occurrence of the datatypes being declared`, as code points.
pub const M_NON_VALID: [u32; 71] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    110, 111, 110, 32, 118, 97, 108, 105, 100, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101,
    32, 111, 102, 32, 116, 104, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115, 32, 98, 101,
    105, 110, 103, 32, 100, 101, 99, 108, 97, 114, 101, 100,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: container vanished`, as code points.
pub const M_VANISHED: [u32; 37] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32, 99,
    111, 110, 116, 97, 105, 110, 101, 114, 32, 118, 97, 110, 105, 115, 104, 101, 100,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: incorrect number of universe levels for a nested inductive datatype (official: incorrect number of universe levels)`, as code points.
pub const M_LEVELS: [u32; 134] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32,
    117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115, 32, 102, 111, 114,
    32, 97, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32,
    100, 97, 116, 97, 116, 121, 112, 101, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32,
    105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32,
    117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)`, as code points.
pub const M_NO_PARAMS: [u32; 129] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    105, 110, 118, 97, 108, 105, 100, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99,
    116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 44, 32, 105, 116, 115, 32, 116,
    121, 112, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 98, 105, 110, 100, 32, 105, 116,
    115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 40, 111, 102, 102, 105, 99, 105,
    97, 108, 58, 32, 105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 105, 110, 100, 117, 99,
    116, 105, 118, 101, 32, 116, 121, 112, 101, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: invalid nested inductive datatype, its type is not a telescope ending in a sort (official: type expected)`, as code points.
pub const M_NOT_SORT: [u32; 124] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    105, 110, 118, 97, 108, 105, 100, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99,
    116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 44, 32, 105, 116, 115, 32, 116,
    121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 101, 108, 101, 115, 99, 111,
    112, 101, 32, 101, 110, 100, 105, 110, 103, 32, 105, 110, 32, 97, 32, 115, 111, 114, 116, 32,
    40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 116, 121, 112, 101, 32, 101, 120, 112, 101,
    99, 116, 101, 100, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: a container's index telescope mentions the block (official: unknown constant)`, as code points.
pub const M_IDX_MENTIONS: [u32; 96] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32, 97,
    32, 99, 111, 110, 116, 97, 105, 110, 101, 114, 39, 115, 32, 105, 110, 100, 101, 120, 32, 116,
    101, 108, 101, 115, 99, 111, 112, 101, 32, 109, 101, 110, 116, 105, 111, 110, 115, 32, 116,
    104, 101, 32, 98, 108, 111, 99, 107, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 117,
    110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: mutually inductive types must live in the same universe`, as code points.
pub const M_UNIVERSE: [u32; 74] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    109, 117, 116, 117, 97, 108, 108, 121, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116,
    121, 112, 101, 115, 32, 109, 117, 115, 116, 32, 108, 105, 118, 101, 32, 105, 110, 32, 116, 104,
    101, 32, 115, 97, 109, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: invalid nested inductive datatype, its constructor has a duplicate universe level parameter (official: duplicate universe level parameter)`, as code points.
pub const M_DUP_ULP: [u32; 157] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    105, 110, 118, 97, 108, 105, 100, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99,
    116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 44, 32, 105, 116, 115, 32, 99,
    111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 104, 97, 115, 32, 97, 32, 100, 117, 112,
    108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101,
    108, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 40, 111, 102, 102, 105, 99, 105, 97,
    108, 58, 32, 100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115,
    101, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: invalid nested inductive datatype, its constructor type does not bind the parameters (official: ill-formed constructor)`, as code points.
pub const M_CTOR_PARAMS: [u32; 138] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    105, 110, 118, 97, 108, 105, 100, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99,
    116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 44, 32, 105, 116, 115, 32, 99,
    111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 121, 112, 101, 32, 100, 111, 101,
    115, 32, 110, 111, 116, 32, 98, 105, 110, 100, 32, 116, 104, 101, 32, 112, 97, 114, 97, 109,
    101, 116, 101, 114, 115, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 105, 108, 108,
    45, 102, 111, 114, 109, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: invalid nested inductive datatype, its constructor type does not bind its fields (official: ill-formed constructor)`, as code points.
pub const M_CTOR_FIELDS: [u32; 134] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    105, 110, 118, 97, 108, 105, 100, 32, 110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99,
    116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 44, 32, 105, 116, 115, 32, 99,
    111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 121, 112, 101, 32, 100, 111, 101,
    115, 32, 110, 111, 116, 32, 98, 105, 110, 100, 32, 105, 116, 115, 32, 102, 105, 101, 108, 100,
    115, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 105, 108, 108, 45, 102, 111, 114,
    109, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: non valid occurrence of the datatypes being declared (a later field or the result depends on a recursive or nested field)`, as code points.
pub const M_U4: [u32; 140] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    110, 111, 110, 32, 118, 97, 108, 105, 100, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101,
    32, 111, 102, 32, 116, 104, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115, 32, 98, 101,
    105, 110, 103, 32, 100, 101, 99, 108, 97, 114, 101, 100, 32, 40, 97, 32, 108, 97, 116, 101,
    114, 32, 102, 105, 101, 108, 100, 32, 111, 114, 32, 116, 104, 101, 32, 114, 101, 115, 117, 108,
    116, 32, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 97, 32, 114, 101, 99, 117, 114,
    115, 105, 118, 101, 32, 111, 114, 32, 110, 101, 115, 116, 101, 100, 32, 102, 105, 101, 108,
    100, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: invalid return type — a constructor's result index mentions the block`, as code points.
pub const M_RET: [u32; 88] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 116, 117, 114, 110, 32, 116, 121, 112, 101, 32,
    8212, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 39, 115, 32, 114, 101,
    115, 117, 108, 116, 32, 105, 110, 100, 101, 120, 32, 109, 101, 110, 116, 105, 111, 110, 115,
    32, 116, 104, 101, 32, 98, 108, 111, 99, 107,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: number of parameters mismatch in inductive datatype declaration (a container's group)`, as code points.
pub const M_GROUP_PARAMS: [u32; 104] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
    32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 105, 110, 100, 117, 99, 116, 105,
    118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116,
    105, 111, 110, 32, 40, 97, 32, 99, 111, 110, 116, 97, 105, 110, 101, 114, 39, 115, 32, 103,
    114, 111, 117, 112, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: non valid occurrence of the datatypes being declared (an instantiation in progress, reached through reduction)`, as code points.
pub const M_IN_PROGRESS: [u32; 129] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    110, 111, 110, 32, 118, 97, 108, 105, 100, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101,
    32, 111, 102, 32, 116, 104, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115, 32, 98, 101,
    105, 110, 103, 32, 100, 101, 99, 108, 97, 114, 101, 100, 32, 40, 97, 110, 32, 105, 110, 115,
    116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 32, 105, 110, 32, 112, 114, 111, 103, 114, 101,
    115, 115, 44, 32, 114, 101, 97, 99, 104, 101, 100, 32, 116, 104, 114, 111, 117, 103, 104, 32,
    114, 101, 100, 117, 99, 116, 105, 111, 110, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: nested inductive datatypes parameters cannot contain local variables`, as code points.
pub const M_LOCAL_VARS: [u32; 87] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    110, 101, 115, 116, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116,
    97, 116, 121, 112, 101, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 99, 97,
    110, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 108, 111, 99, 97, 108, 32, 118,
    97, 114, 105, 97, 98, 108, 101, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: type expected (a container instance that is not fully applied)`, as code points.
pub const M_NOT_FULL: [u32; 81] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    116, 121, 112, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 40, 97, 32, 99, 111, 110,
    116, 97, 105, 110, 101, 114, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 116, 104, 97, 116,
    32, 105, 115, 32, 110, 111, 116, 32, 102, 117, 108, 108, 121, 32, 97, 112, 112, 108, 105, 101,
    100, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: fuel`, as code points.
pub const M_FUEL: [u32; 23] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    102, 117, 101, 108,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `nested positivity: non positive occurrence of the datatypes being declared`, as code points.
pub const M_NON_POSITIVE: [u32; 74] = [
    110, 101, 115, 116, 101, 100, 32, 112, 111, 115, 105, 116, 105, 118, 105, 116, 121, 58, 32,
    110, 111, 110, 32, 112, 111, 115, 105, 116, 105, 118, 101, 32, 111, 99, 99, 117, 114, 114, 101,
    110, 99, 101, 32, 111, 102, 32, 116, 104, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115,
    32, 98, 101, 105, 110, 103, 32, 100, 101, 99, 108, 97, 114, 101, 100,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `invalid occurrence of a datatype being declared in the type of : it must be applied to the parameters and universe levels of the mutual declaration`, as code points.
pub const M_UNIFORM: [u32; 147] = [
    105, 110, 118, 97, 108, 105, 100, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 111,
    102, 32, 97, 32, 100, 97, 116, 97, 116, 121, 112, 101, 32, 98, 101, 105, 110, 103, 32, 100,
    101, 99, 108, 97, 114, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 32,
    111, 102, 32, 58, 32, 105, 116, 32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 112, 112, 108,
    105, 101, 100, 32, 116, 111, 32, 116, 104, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114,
    115, 32, 97, 110, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108,
    115, 32, 111, 102, 32, 116, 104, 101, 32, 109, 117, 116, 117, 97, 108, 32, 100, 101, 99, 108,
    97, 114, 97, 116, 105, 111, 110,
];

// ---------------------------------------------------------------------------
// `mentionsAnyConst`: the positivity walk's question at k names
// ---------------------------------------------------------------------------

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean mentionsAnyGo` — the
/// `memo[e]?` probe of a Boolean walk (shared by `mentionsAnyConst` and
/// `nestOcc`).
pub fn memo_bool_probe(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: none — `List.contains` on a name-handle list, which is handle equality (DESIGN.md §8.3)
/// Lean twin: `names.contains n`.
pub fn names_contain(ns: &Vec<NIdx>, n: &NIdx, i: usize) -> bool {
    if i >= ns.len() {
        false
    } else if ns[i].eq2(n) {
        true
    } else {
        names_contain(ns, n, i + 1)
    }
}

/// con-leche: none — `List.findIdx? (· == n)` on a name-handle list
/// Lean twin: `names.findIdx? (· == n)`.
pub fn names_find_idx(ns: &Vec<NIdx>, n: &NIdx, i: usize) -> Option<u64> {
    if i >= ns.len() {
        None
    } else if ns[i].eq2(n) {
        Some(i as u64)
    } else {
        names_find_idx(ns, n, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:42-54 Expr.mentionsAnyConst
/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:84-119 Expr.mentionsAnyGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean mentionsAnyGo` —
/// does any of the constants `names` occur in `e`?  A syntactic walk (`fvar`
/// annotations included; a `.proj` node names its structure), memoised on
/// the node.  The executed walk evaluates BOTH children of a binary node (no
/// short circuit), as con-leche's `mentionsAnyGo` does.
pub fn mentions_any_go(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_MENTIONS_ANY)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((false, memo)),
            Ok(ENodeView::Sort(_)) => Ok((false, memo)),
            Ok(ENodeView::Lit(_)) => Ok((false, memo)),
            Ok(ENodeView::Const(n, _)) => Ok((names_contain(names, &n, 0), memo)),
            Ok(v) => match memo_bool_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match mentions_any_node(pers, st, names, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, bool> = m;
                        m2.insert(h.dup2(), r);
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:84-119 Expr.mentionsAnyGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean mentionsAnyGo` — the
/// walk's compound arms.
pub fn mentions_any_node(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::FVar(_, ty) => mentions_any_go(pers, st, names, memo, fuel, &ty),
        ENodeView::App(f, a) => match mentions_any_go(pers, st, names, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok((b1, m)) => match mentions_any_go(pers, st, names, m, fuel, &a) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 || b2, m2)),
            },
        },
        ENodeView::Lam(ty, body, _) => match mentions_any_go(pers, st, names, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match mentions_any_go(pers, st, names, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 || b2, m2)),
            },
        },
        ENodeView::ForallE(ty, body, _) => {
            match mentions_any_go(pers, st, names, memo, fuel, &ty) {
                Err(e) => Err(e),
                Ok((b1, m)) => match mentions_any_go(pers, st, names, m, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b2, m2)) => Ok((b1 || b2, m2)),
                },
            }
        }
        ENodeView::LetE(ty, val, body) => {
            match mentions_any_go(pers, st, names, memo, fuel, &ty) {
                Err(e) => Err(e),
                Ok((b1, m)) => match mentions_any_go(pers, st, names, m, fuel, &val) {
                    Err(e) => Err(e),
                    Ok((b2, m2)) => match mentions_any_go(pers, st, names, m2, fuel, &body) {
                        Err(e) => Err(e),
                        Ok((b3, m3)) => Ok((b1 || b2 || b3, m3)),
                    },
                },
            }
        }
        ENodeView::Proj(s, _, sub) => match mentions_any_go(pers, st, names, memo, fuel, &sub) {
            Err(e) => Err(e),
            Ok((b, m)) => Ok((names_contain(names, &s, 0) || b, m)),
        },
        _ => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:192-194 Expr.mentionsAnyConstFast
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean mentionsAnyConst` —
/// the executed `mentionsAnyConst` (one memoised DAG walk).
pub fn mentions_any_const(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match mentions_any_go(pers, st, names, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:201-207 memberIdxAt?
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean memberIdxAt?` — which
/// member of the block a head expression names, at the block's own level
/// parameters `lvls` (an interned list, so the cited `us == lvls` is handle
/// equality); `none` at any other head.
pub fn member_idx_at(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    e: &EIdx,
) -> Result<Option<u64>, CheckError> {
    if e.tag() == ETAG_CONST {
        match view_const(pers, st, e) {
            None => fail_dangling_e(),
            Some((n, us)) => {
                if us.eq2(lvls) {
                    Ok(names_find_idx(names, &n, 0))
                } else {
                    Ok(None)
                }
            }
        }
    } else {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// Closing a telescope
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:211-219 closeTelescope
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean closeTelescope` —
/// close a telescope opened at the free variables `i ..< i + bs.length` back
/// into a syntactic Π-telescope over `body`.  The cursor recursion builds the
/// innermost binder first, as the cited `closeTelescope bs (i + 1) body` does.
pub fn close_telescope(
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
        match close_telescope(pers, st, bs, k + 1, i + 1, body) {
            Err(e) => Err(e),
            Ok(inner) => match expr_ops::abstract1_fast(pers, st, CORE_WALK_FUEL, &inner, i, 0) {
                Err(e) => Err(e),
                Ok(closed) => {
                    let dom: EIdx = bs[k].0.dup2();
                    let bm: BinderMeta = expr::binder_meta_dup(&bs[k].1);
                    intern_e_forall_e(pers, st, dom, closed, bm)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// `nestOcc`: official's `has_ind_occ`, with the holes
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:328-345 Expr.nestOcc
/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:347-377 Expr.nestOccGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestOccGo` — does a
/// MEMBER or a HOLE (the free variables `lo ..< hi`) occur in `e`?  A free
/// variable's annotation is NOT looked into, and a `.proj` node's structure
/// name is no occurrence.  Short-circuiting, memoised on the node.
pub fn nest_occ_go(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lo: u64,
    hi: u64,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_NEST_OCC)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((false, memo)),
            Ok(ENodeView::Sort(_)) => Ok((false, memo)),
            Ok(ENodeView::Lit(_)) => Ok((false, memo)),
            Ok(ENodeView::FVar(i, _)) => Ok((lo <= i && i < hi, memo)),
            Ok(ENodeView::Const(n, _)) => Ok((names_contain(names, &n, 0), memo)),
            Ok(v) => match memo_bool_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match nest_occ_node(pers, st, names, lo, hi, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, bool> = m;
                        m2.insert(h.dup2(), r);
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:347-377 Expr.nestOccGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestOccGo` — the
/// walk's compound arms, each a short circuit.
pub fn nest_occ_node(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lo: u64,
    hi: u64,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::App(f, a) => match nest_occ_go(pers, st, names, lo, hi, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => nest_occ_go(pers, st, names, lo, hi, m, fuel, &a),
        },
        ENodeView::Lam(ty, body, _) => match nest_occ_go(pers, st, names, lo, hi, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => nest_occ_go(pers, st, names, lo, hi, m, fuel, &body),
        },
        ENodeView::ForallE(ty, body, _) => {
            match nest_occ_go(pers, st, names, lo, hi, memo, fuel, &ty) {
                Err(e) => Err(e),
                Ok((true, m)) => Ok((true, m)),
                Ok((false, m)) => nest_occ_go(pers, st, names, lo, hi, m, fuel, &body),
            }
        }
        ENodeView::LetE(ty, val, body) => {
            match nest_occ_go(pers, st, names, lo, hi, memo, fuel, &ty) {
                Err(e) => Err(e),
                Ok((true, m)) => Ok((true, m)),
                Ok((false, m)) => match nest_occ_go(pers, st, names, lo, hi, m, fuel, &val) {
                    Err(e) => Err(e),
                    Ok((true, m2)) => Ok((true, m2)),
                    Ok((false, m2)) => nest_occ_go(pers, st, names, lo, hi, m2, fuel, &body),
                },
            }
        }
        ENodeView::Proj(_, _, sub) => nest_occ_go(pers, st, names, lo, hi, memo, fuel, &sub),
        _ => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:506-508 Expr.nestOccFast
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestOcc` — the
/// executed `nestOcc` (one memoised DAG walk).
pub fn nest_occ(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lo: u64,
    hi: u64,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match nest_occ_go(pers, st, names, lo, hi, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:328-345 Expr.nestOcc
/// Lean twin: `xs.any (·.nestOcc names lo hi)` — some element of `xs[i..]`
/// mentions a member or a hole (in order, stopping at the first).
pub fn nest_occ_any(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lo: u64,
    hi: u64,
    xs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= xs.len() {
        Ok(false)
    } else {
        let x: EIdx = xs[i].dup2();
        match nest_occ(pers, st, names, lo, hi, &x) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => nest_occ_any(pers, st, names, lo, hi, xs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:328-345 Expr.nestOcc
/// Lean twin: `bs.any (fun b => b.1.nestOcc names lo hi)` over a binder list.
pub fn nest_occ_any_binder(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lo: u64,
    hi: u64,
    bs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= bs.len() {
        Ok(false)
    } else {
        let x: EIdx = bs[i].0.dup2();
        match nest_occ(pers, st, names, lo, hi, &x) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => nest_occ_any_binder(pers, st, names, lo, hi, bs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:514-519 instPisWith
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean instPisWith` —
/// instantiate the leading `Π` binders of `e` at `args[i..]`, in order.
pub fn inst_pis_with(
    pers: &PersTier,
    st: &mut AState,
    args: &Vec<EIdx>,
    i: usize,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if i >= args.len() {
        Ok(Some(e.dup2()))
    } else if e.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, e) {
            None => fail_dangling_e(),
            Some((_, body, _)) => {
                let a: EIdx = args[i].dup2();
                match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &a, 0) {
                    Err(er) => Err(er),
                    Ok(b) => inst_pis_with(pers, st, args, i + 1, &b),
                }
            }
        }
    } else {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// The records
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestKey` — a
/// container INSTANTIATION `C.{lvls} Ds`, the key of the only cache there
/// is.  `lvls` is the interned level list (a `const` node's own).
pub struct NestKey {
    pub cname: NIdx,
    pub lvls: LsIdx,
    pub ds: Vec<EIdx>,
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey
/// The record copy.
pub fn nest_key_dup(k: &NestKey) -> NestKey {
    NestKey {
        cname: k.cname.dup2(),
        lvls: k.lvls.dup2(),
        ds: env::eidx_vec_dup(&k.ds),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey
/// The cited `deriving DecidableEq`: handle equality componentwise.
pub fn nest_key_beq(a: &NestKey, b: &NestKey) -> bool {
    a.cname.eq2(&b.cname) && a.lvls.eq2(&b.lvls) && crate::arena::canon::eidx_vec_beq(&a.ds, &b.ds, 0)
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey
/// `keys.contains k` over a key list (`Array.contains`/`List.contains`).
pub fn nest_keys_contain(keys: &Vec<NestKey>, k: &NestKey, i: usize) -> bool {
    if i >= keys.len() {
        false
    } else if nest_key_beq(&keys[i], k) {
        true
    } else {
        nest_keys_contain(keys, k, i + 1)
    }
}

/// con-leche: none — a `List NestKey` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestState`.
pub fn nest_keys_dup(ks: &Vec<NestKey>, i: usize, out: Vec<NestKey>) -> Vec<NestKey> {
    if i >= ks.len() {
        out
    } else {
        let mut o: Vec<NestKey> = out;
        o.push(nest_key_dup(&ks[i]));
        nest_keys_dup(ks, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:530-536 NestHole
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestHole` — a HOLE
/// of the walk: the instantiation it stands for, and the first hole index of
/// its frame.
pub struct NestHole {
    pub key: NestKey,
    pub base: u64,
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:530-536 NestHole
/// The record copy.
pub fn nest_hole_dup(h: &NestHole) -> NestHole {
    NestHole {
        key: nest_key_dup(&h.key),
        base: h.base,
    }
}

/// con-leche: none — a `List NestHole` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestHole`.
pub fn nest_holes_dup(hs: &Vec<NestHole>, i: usize, out: Vec<NestHole>) -> Vec<NestHole> {
    if i >= hs.len() {
        out
    } else {
        let mut o: Vec<NestHole> = out;
        o.push(nest_hole_dup(&hs[i]));
        nest_holes_dup(hs, i + 1, o)
    }
}

// ---------------------------------------------------------------------------
// The input-derived fuel
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:553-554 fuelSlack
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean fuelSlack` — the
/// fuel's slack above the term's depth.
pub const FUEL_SLACK: u64 = 1024;

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean depthGo` — the
/// `memo[e]?` probe of the depth walk.
pub fn depth_probe(memo: &HashMap<EIdx, u64>, k: &EIdx) -> Option<u64> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: none — `max a b` on `u64`, spelled as a branch (`Ord`/`max` is out of the Aeneas subset, AENEAS_FINDINGS §2.2)
/// Lean twin: `max`.
pub fn max_u64(a: u64, b: u64) -> u64 {
    if a < b {
        b
    } else {
        a
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-588 Expr.depthGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean depthGo` — the
/// longest root-to-leaf path (`fvar` annotations not descended), memoised on
/// the node, so a DAG costs its distinct nodes.
pub fn depth_go(
    pers: &PersTier,
    st: &AState,
    memo: HashMap<EIdx, u64>,
    fuel: u64,
    h: &EIdx,
) -> Result<(u64, HashMap<EIdx, u64>), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_DEPTH)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((1, memo)),
            Ok(ENodeView::FVar(_, _)) => Ok((1, memo)),
            Ok(ENodeView::Sort(_)) => Ok((1, memo)),
            Ok(ENodeView::Const(_, _)) => Ok((1, memo)),
            Ok(ENodeView::Lit(_)) => Ok((1, memo)),
            Ok(v) => match depth_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match depth_node(pers, st, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, u64> = m;
                        m2.insert(h.dup2(), r);
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-588 Expr.depthGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean depthGo` — the
/// walk's compound arms.
pub fn depth_node(
    pers: &PersTier,
    st: &AState,
    memo: HashMap<EIdx, u64>,
    fuel: u64,
    v: ENodeView,
) -> Result<(u64, HashMap<EIdx, u64>), CheckError> {
    match v {
        ENodeView::App(f, a) => match depth_go(pers, st, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok((d1, m)) => match depth_go(pers, st, m, fuel, &a) {
                Err(e) => Err(e),
                Ok((d2, m2)) => Ok((max_u64(d1, d2) + 1, m2)),
            },
        },
        ENodeView::Lam(ty, body, _) => match depth_go(pers, st, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((d1, m)) => match depth_go(pers, st, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((d2, m2)) => Ok((max_u64(d1, d2) + 1, m2)),
            },
        },
        ENodeView::ForallE(ty, body, _) => match depth_go(pers, st, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((d1, m)) => match depth_go(pers, st, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((d2, m2)) => Ok((max_u64(d1, d2) + 1, m2)),
            },
        },
        ENodeView::LetE(ty, val, body) => match depth_go(pers, st, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((d1, m)) => match depth_go(pers, st, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((d2, m2)) => match depth_go(pers, st, m2, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((d3, m3)) => Ok((max_u64(max_u64(d1, d2), d3) + 1, m3)),
                },
            },
        },
        ENodeView::Proj(_, _, x) => match depth_go(pers, st, memo, fuel, &x) {
            Err(e) => Err(e),
            Ok((d, m)) => Ok((d + 1, m)),
        },
        _ => Ok((1, memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:590-592 Expr.depth
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean depth` — a term's
/// depth, memoised.
pub fn expr_depth(pers: &PersTier, st: &AState, e: &EIdx) -> Result<u64, CheckError> {
    match depth_go(pers, st, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:594-596 whnfWalkFuel
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean whnfWalkFuel` —
/// the fuel of a walk through whnf starting at `e`: its depth plus the slack.
pub fn whnf_walk_fuel(pers: &PersTier, st: &AState, e: &EIdx) -> Result<u64, CheckError> {
    match expr_depth(pers, st, e) {
        Err(er) => Err(er),
        Ok(d) => Ok(d + FUEL_SLACK),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:598-608 NestFieldKind
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestFieldKind` — the
/// field's kind as the run found it.
pub enum NestFieldKind {
    Ordinary,
    Recursive(u64),
    Reflexive(u64),
    InProgress,
    Nested(bool),
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:598-608 NestFieldKind
/// The copy.
pub fn nest_field_kind_dup(k: &NestFieldKind) -> NestFieldKind {
    match k {
        NestFieldKind::Ordinary => NestFieldKind::Ordinary,
        NestFieldKind::Recursive(t) => NestFieldKind::Recursive(*t),
        NestFieldKind::Reflexive(t) => NestFieldKind::Reflexive(*t),
        NestFieldKind::InProgress => NestFieldKind::InProgress,
        NestFieldKind::Nested(r) => NestFieldKind::Nested(*r),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:598-608 NestFieldKind
/// `k != .ordinary`, the cited `DecidableEq` at the one comparison the walk
/// makes (U4).
pub fn nest_field_kind_is_ordinary(k: &NestFieldKind) -> bool {
    match k {
        NestFieldKind::Ordinary => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:610-613 NestFieldKind.flat
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestFieldKind.flat`
/// — a field kind the uniform route installs: no container instantiation.
pub fn nest_field_kind_flat(k: &NestFieldKind) -> bool {
    match k {
        NestFieldKind::Ordinary => true,
        NestFieldKind::Recursive(_) => true,
        NestFieldKind::Reflexive(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:615-619 nestKindsFlat
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestKindsFlat` —
/// every field of every constructor of every member is flat.  The three
/// nested `all`s are one index recursion per level.
pub fn nest_kinds_flat(kss: &Vec<Vec<Vec<NestFieldKind>>>, i: usize) -> bool {
    if i >= kss.len() {
        true
    } else if nest_kinds_flat_member(&kss[i], 0) {
        nest_kinds_flat(kss, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:615-619 nestKindsFlat
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestKindsFlat` — one
/// member's constructors.
pub fn nest_kinds_flat_member(ks: &Vec<Vec<NestFieldKind>>, i: usize) -> bool {
    if i >= ks.len() {
        true
    } else if nest_kinds_flat_ctor(&ks[i], 0) {
        nest_kinds_flat_member(ks, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:615-619 nestKindsFlat
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestKindsFlat` — one
/// constructor's fields.
pub fn nest_kinds_flat_ctor(ks: &Vec<NestFieldKind>, i: usize) -> bool {
    if i >= ks.len() {
        true
    } else if nest_field_kind_flat(&ks[i]) {
        nest_kinds_flat_ctor(ks, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:621-641 NestCtorNf
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestCtorNf` — a
/// constructor's walked normal form, recorded (K.53′): the constructor, the
/// class's levels and parameters, and its walked field telescope, all read
/// back.
pub struct NestCtorNf {
    pub ctor: NIdx,
    pub lvls: LsIdx,
    pub ds: Vec<EIdx>,
    pub ty: EIdx,
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:621-641 NestCtorNf
/// The record copy.
pub fn nest_ctor_nf_dup(e: &NestCtorNf) -> NestCtorNf {
    NestCtorNf {
        ctor: e.ctor.dup2(),
        lvls: e.lvls.dup2(),
        ds: env::eidx_vec_dup(&e.ds),
        ty: e.ty.dup2(),
    }
}

/// con-leche: none — a `List NestCtorNf` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestCtorNf`.
pub fn nest_ctor_nfs_dup(es: &Vec<NestCtorNf>, i: usize, out: Vec<NestCtorNf>) -> Vec<NestCtorNf> {
    if i >= es.len() {
        out
    } else {
        let mut o: Vec<NestCtorNf> = out;
        o.push(nest_ctor_nf_dup(&es[i]));
        nest_ctor_nfs_dup(es, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:643-654 NestCtx
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestCtx` — the
/// block, as the function needs it.  `find?` is `(vis, fe)` (the module
/// note): the record carries the visibility bound and every reader takes the
/// environment beside it.  `lvls` is `lps.map .param`, interned once.
pub struct NestCtx {
    pub names: Vec<NIdx>,
    pub lps: Vec<NIdx>,
    pub n_p: u64,
    pub n_idxs: Vec<u64>,
    pub params: Vec<EIdx>,
    pub sort: LIdx,
    pub vis: u64,
    pub lvls: LsIdx,
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:643-654 NestCtx
/// The record copy.
pub fn nest_ctx_dup(c: &NestCtx) -> NestCtx {
    NestCtx {
        names: env::nidx_vec_dup(&c.names),
        lps: env::nidx_vec_dup(&c.lps),
        n_p: c.n_p,
        n_idxs: u64_vec_dup(&c.n_idxs, 0, Vec::new()),
        params: env::eidx_vec_dup(&c.params),
        sort: c.sort.dup2(),
        vis: c.vis,
        lvls: c.lvls.dup2(),
    }
}

/// con-leche: none — a `List Nat` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestCtx`.
pub fn u64_vec_dup(xs: &Vec<u64>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<u64> = out;
        o.push(xs[i]);
        u64_vec_dup(xs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:656-668 NestState
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestState` — the
/// run's state: the accepted instantiations (the cache), the instantiations
/// in progress, and every derived node's constructors normalised and read
/// back, in walk order.
pub struct NestState {
    pub keys: Vec<NestKey>,
    pub active: Vec<NestKey>,
    pub ctor_nfs: Vec<NestCtorNf>,
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:656-668 NestState
/// The empty state, the cited structure's field defaults.
pub fn nest_state_empty() -> NestState {
    NestState {
        keys: Vec::new(),
        active: Vec::new(),
        ctor_nfs: Vec::new(),
    }
}

// ---------------------------------------------------------------------------
// Containers
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:684-695 nestCtorEntry
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtorEntry` — a
/// stored constant's entry as a constructor of `C`: a constructor record
/// whose result, past its parameters and fields, is headed by `C`.
pub fn nest_ctor_entry(
    pers: &PersTier,
    st: &AState,
    c: &NIdx,
    ci: &IConstantInfo,
) -> Result<Option<(IConstantVal, u64, u64)>, CheckError> {
    match ci {
        IConstantInfo::CtorInfo(cv, n_pc, n_f) => {
            match expr_ops::strip_pis(pers, st, *n_pc + *n_f, &cv.ty) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(q)) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &q.1) {
                    Err(e) => Err(e),
                    Ok(hd) => {
                        if hd.tag() == ETAG_CONST {
                            match view_const(pers, st, &hd) {
                                None => fail_dangling_e(),
                                Some((n, _)) => {
                                    if n.eq2(c) {
                                        Ok(Some((env::i_constant_val_dup(cv), *n_pc, *n_f)))
                                    } else {
                                        Ok(None)
                                    }
                                }
                            }
                        } else {
                            Ok(None)
                        }
                    }
                },
            }
        }
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:697-712 nestContainer
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestContainer` —
/// the `indInfo` lookup, its recorded parameter count and constructor names
/// read out (so no loan into the environment spans the constructor
/// lookups, extraction rule 1).
pub fn ind_caps_ctors(vis: u64, fe: &IFEnv, c: &NIdx) -> Option<(u64, Vec<NIdx>)> {
    match env::ifenv_find(vis, fe, c) {
        Some(IConstantInfo::IndInfo(_, caps)) => Some((caps.nparams, env::nidx_vec_dup(&caps.ctors))),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:697-712 nestContainer
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestContainer` —
/// `caps.ctors.filterMap fun n => (find? n).bind (nestCtorEntry C)`, as an
/// index recursion.
pub fn nest_container_ctors(
    pers: &PersTier,
    st: &AState,
    vis: u64,
    fe: &IFEnv,
    c: &NIdx,
    ns: &Vec<NIdx>,
    i: usize,
    out: Vec<(IConstantVal, u64, u64)>,
) -> Result<Vec<(IConstantVal, u64, u64)>, CheckError> {
    if i >= ns.len() {
        Ok(out)
    } else {
        match nest_ctor_entry_of(pers, st, vis, fe, c, &ns[i]) {
            Err(e) => Err(e),
            Ok(Some(x)) => {
                let mut o: Vec<(IConstantVal, u64, u64)> = out;
                o.push(x);
                nest_container_ctors(pers, st, vis, fe, c, ns, i + 1, o)
            }
            Ok(None) => nest_container_ctors(pers, st, vis, fe, c, ns, i + 1, out),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:697-712 nestContainer
/// Lean twin: `(find? n).bind (nestCtorEntry C)` — one listed constructor
/// name looked up and read as an entry of `C`.
pub fn nest_ctor_entry_of(
    pers: &PersTier,
    st: &AState,
    vis: u64,
    fe: &IFEnv,
    c: &NIdx,
    n: &NIdx,
) -> Result<Option<(IConstantVal, u64, u64)>, CheckError> {
    match env::ifenv_find(vis, fe, n) {
        Some(ci) => nest_ctor_entry(pers, st, c, ci),
        None => Ok(None),
    }
}

/// con-leche: none — `cs.map fun c => (c.1, c.2.2)`
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestContainer`.
pub fn ctor_entries_nf(
    cs: &Vec<(IConstantVal, u64, u64)>,
    i: usize,
    out: Vec<(IConstantVal, u64)>,
) -> Vec<(IConstantVal, u64)> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<(IConstantVal, u64)> = out;
        o.push((env::i_constant_val_dup(&cs[i].0), cs[i].2));
        ctor_entries_nf(cs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:697-712 nestContainer
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestContainer` —
/// the constructors of the inductive `C` and its parameter count, looked up
/// by the names its stored record lists (`IndCaps.ctors`); for an inductive
/// without constructors its RECORDED parameter count (`IndCaps.nparams`);
/// `none` when `C` is no inductive.  Takes the lookup `(vis, fe)` rather than
/// the whole context: `targetCtorsOf` calls it with a context whose only
/// field it reads is `find?`.
pub fn nest_container(
    pers: &PersTier,
    st: &AState,
    vis: u64,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<Option<(u64, Vec<(IConstantVal, u64)>)>, CheckError> {
    match ind_caps_ctors(vis, fe, c) {
        None => Ok(None),
        Some((n_params, ns)) => match nest_container_ctors(pers, st, vis, fe, c, &ns, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(cs) => {
                if cs.len() == 0 {
                    Ok(Some((n_params, Vec::new())))
                } else {
                    let n_pc: u64 = cs[0].1;
                    Ok(Some((n_pc, ctor_entries_nf(&cs, 0, Vec::new()))))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:714-716 nestNonValid
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestNonValid` —
/// official's "non valid occurrence".
pub fn nest_non_valid() -> CheckError {
    core_types::invalid(code_points(&M_NON_VALID))
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:718-721 NestCtx.hiAt
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestCtx.hiAt` — the
/// first hole-free variable index of a walk under `nf` frames.
pub fn hi_at(ctx: &NestCtx, nf: u64) -> u64 {
    ctx.n_p + (ctx.names.len() as u64) + nf
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:723-727 NestCtx.rootHoles
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean NestCtx.rootHoles` —
/// the ROOT frame's entries: each member at the block's own levels and
/// canonical parameters, base `nP`.  (Entry `j`, as `nest_hole_at` reads it.)
pub fn root_hole(ctx: &NestCtx, j: usize) -> NestHole {
    NestHole {
        key: NestKey {
            cname: ctx.names[j].dup2(),
            lvls: ctx.lvls.dup2(),
            ds: env::eidx_vec_dup(&ctx.params),
        },
        base: ctx.n_p,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:729-734 nestHoleAt
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestHoleAt` — the
/// hole `i`'s entry under the frames `prog`: the stack read root first — the
/// root frame's entries, then `prog` from the outside (the Rust `prog` IS
/// that order, the module note); `none` off the holes.
pub fn nest_hole_at(ctx: &NestCtx, prog: &Vec<NestHole>, i: u64) -> Option<NestHole> {
    if ctx.n_p <= i {
        let j: u64 = i - ctx.n_p;
        let k: u64 = ctx.names.len() as u64;
        if j < k {
            Some(root_hole(ctx, j as usize))
        } else if j - k < prog.len() as u64 {
            Some(nest_hole_dup(&prog[(j - k) as usize]))
        } else {
            None
        }
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// Reading a walked term back: `replaceFVars` and its four maps
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:884-900 nestHoleImg
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestHoleImg` — the
/// data `nestHoleImg ctx prog` reads, owned: the context, the frame stack and
/// the length `n` of the stack prefix it is applied to (the module note).
pub struct HoleImgMap {
    pub ctx: NestCtx,
    pub prog: Vec<NestHole>,
    pub n: u64,
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean FvMap` — the
/// function argument of `replaceFVars`, one variant per instantiation
/// con-leche writes (the module note): `nestHoleImg ctx prog`, `nestKeyMap ds
/// holes`, `eraseFVarTys`' `fun i => some (.fvar i (.sort .zero))` and
/// `targetCanonParams`' `fun i => pfvs[i]?`.
pub enum FvMap {
    HoleImg(HoleImgMap),
    KeyMap(Vec<EIdx>, Vec<EIdx>),
    Erase,
    Canon(Vec<EIdx>),
}

/// con-leche: none — `(.sort .zero)`, the placeholder annotation of the canonical variables
/// Lean twin: `.sort .zero`.
pub fn sort_zero(pers: &PersTier, st: &mut AState) -> Result<EIdx, CheckError> {
    match core::zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => intern_e_sort(pers, st, z),
    }
}

/// con-leche: none — `xs[i]?` on a handle list at a `Nat` index
/// Lean twin: `xs[i]?`.
pub fn eidx_get(xs: &Vec<EIdx>, i: u64) -> Option<EIdx> {
    if i < xs.len() as u64 {
        Some(xs[i as usize].dup2())
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean fvMapAt` — the map
/// `f` applied to the variable `i`, by the variant.
pub fn fv_map_at(
    pers: &PersTier,
    st: &mut AState,
    f: &FvMap,
    i: u64,
) -> Result<Option<EIdx>, CheckError> {
    match f {
        FvMap::HoleImg(m) => nest_hole_img(pers, st, &m.ctx, &m.prog, m.n, i),
        FvMap::KeyMap(ds, holes) => Ok(nest_key_map(ds, holes, i)),
        FvMap::Erase => match sort_zero(pers, st) {
            Err(e) => Err(e),
            Ok(s) => match intern_e_fvar(pers, st, i, s) {
                Err(e) => Err(e),
                Ok(v) => Ok(Some(v)),
            },
        },
        FvMap::Canon(pfvs) => Ok(eidx_get(pfvs, i)),
    }
}

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceFVarsGo` —
/// the `memo[e]?` probe of a rebuilding walk (shared by `replaceFVars` and
/// `replaceApps`).
pub fn memo_e_probe(memo: &HashMap<EIdx, EIdx>, k: &EIdx) -> Option<EIdx> {
    match memo.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:775-810 Expr.replaceFVarsGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceFVarsGo` —
/// replace the free variables `f` maps (a mapped variable is replaced whole,
/// its annotation not descended into), memoised on the node.
pub fn replace_fvars_go(
    pers: &PersTier,
    st: &mut AState,
    f: &FvMap,
    memo: HashMap<EIdx, EIdx>,
    fuel: u64,
    h: &EIdx,
) -> Result<(EIdx, HashMap<EIdx, EIdx>), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_REPLACE_FVARS)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Sort(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Lit(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Const(_, _)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::FVar(i, _)) => match fv_map_at(pers, st, f, i) {
                Err(e) => Err(e),
                Ok(Some(r)) => Ok((r, memo)),
                Ok(None) => Ok((h.dup2(), memo)),
            },
            Ok(v) => match memo_e_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match replace_fvars_node(pers, st, f, memo, fuel - 1, h, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, EIdx> = m;
                        m2.insert(h.dup2(), r.dup2());
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:775-810 Expr.replaceFVarsGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceFVarsGo` — the
/// walk's compound arms, each rebuilt.
pub fn replace_fvars_node(
    pers: &PersTier,
    st: &mut AState,
    f: &FvMap,
    memo: HashMap<EIdx, EIdx>,
    fuel: u64,
    h: &EIdx,
    v: ENodeView,
) -> Result<(EIdx, HashMap<EIdx, EIdx>), CheckError> {
    match v {
        ENodeView::App(a, b) => match replace_fvars_go(pers, st, f, memo, fuel, &a) {
            Err(e) => Err(e),
            Ok((a2, m)) => match replace_fvars_go(pers, st, f, m, fuel, &b) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match intern_e_app(pers, st, a2, b2) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((r, m2)),
                },
            },
        },
        ENodeView::Lam(ty, body, bm) => match replace_fvars_go(pers, st, f, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((t2, m)) => match replace_fvars_go(pers, st, f, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match intern_e_lam(pers, st, t2, b2, bm) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((r, m2)),
                },
            },
        },
        ENodeView::ForallE(ty, body, bm) => match replace_fvars_go(pers, st, f, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((t2, m)) => match replace_fvars_go(pers, st, f, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match intern_e_forall_e(pers, st, t2, b2, bm) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((r, m2)),
                },
            },
        },
        ENodeView::LetE(ty, val, body) => match replace_fvars_go(pers, st, f, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((t2, m)) => match replace_fvars_go(pers, st, f, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((v2, m2)) => match replace_fvars_go(pers, st, f, m2, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b2, m3)) => match intern_e_let_e(pers, st, t2, v2, b2) {
                        Err(e) => Err(e),
                        Ok(r) => Ok((r, m3)),
                    },
                },
            },
        },
        ENodeView::Proj(s, i, sub) => match replace_fvars_go(pers, st, f, memo, fuel, &sub) {
            Err(e) => Err(e),
            Ok((u, m)) => match intern_e_proj(pers, st, s, i, u) {
                Err(e) => Err(e),
                Ok(r) => Ok((r, m)),
            },
        },
        // the leaves are answered by `replace_fvars_go` and never reach here
        _ => Ok((h.dup2(), memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:875-877 Expr.replaceFVarsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceFVars` — the
/// executed `replaceFVars` (one memoised DAG walk, a fresh memo per call).
pub fn replace_fvars(
    pers: &PersTier,
    st: &mut AState,
    f: &FvMap,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match replace_fvars_go(pers, st, f, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
/// Lean twin: `xs.map (·.replaceFVars f)` — each element read back, in order.
pub fn replace_fvars_list(
    pers: &PersTier,
    st: &mut AState,
    f: &FvMap,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let x: EIdx = xs[i].dup2();
        match replace_fvars(pers, st, f, &x) {
            Err(e) => Err(e),
            Ok(r) => {
                let mut o: Vec<EIdx> = out;
                o.push(r);
                replace_fvars_list(pers, st, f, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:884-900 nestHoleImg
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestHoleImg` — **the
/// holes read back** under the frames `prog[..n]` (the stack prefix of
/// length `n`, its last element the innermost frame): member `m`'s hole
/// `nP + m` is `T_m.{lps} p⃗`, a frame's hole its container applied to the
/// frame's parameters, themselves read back under the frames below it.
pub fn nest_hole_img(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    prog: &Vec<NestHole>,
    n: u64,
    i: u64,
) -> Result<Option<EIdx>, CheckError> {
    if n == 0 {
        if ctx.n_p <= i && i < hi_at(ctx, 0) {
            let nm: NIdx = ctx.names[(i - ctx.n_p) as usize].dup2();
            match intern_e_const(pers, st, nm, ctx.lvls.dup2()) {
                Err(e) => Err(e),
                Ok(hd) => match expr_ops::mk_app_n(pers, st, &hd, &ctx.params) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(Some(r)),
                },
            }
        } else {
            Ok(None)
        }
    } else if i == hi_at(ctx, n - 1) {
        let h: NestHole = nest_hole_dup(&prog[(n - 1) as usize]);
        let f: FvMap = FvMap::HoleImg(HoleImgMap {
            ctx: nest_ctx_dup(ctx),
            prog: nest_holes_dup(prog, 0, Vec::new()),
            n: n - 1,
        });
        match replace_fvars_list(pers, st, &f, &h.key.ds, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(ds) => match intern_e_const(pers, st, h.key.cname, h.key.lvls) {
                Err(e) => Err(e),
                Ok(hd) => match expr_ops::mk_app_n(pers, st, &hd, &ds) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(Some(r)),
                },
            },
        }
    } else {
        nest_hole_img(pers, st, ctx, prog, n - 1, i)
    }
}

// ---------------------------------------------------------------------------
// The whole-application abstraction (`replaceApps` at `nestCanonSub`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:917-923 Expr.phApp?
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean phApp?` — `e` is a
/// constant applied to EXACTLY the placeholder variables `fvar b, …, fvar (b
/// + n - 1)` (annotations not compared): the constant's name and levels.
pub fn ph_app(
    pers: &PersTier,
    st: &AState,
    b: u64,
    e: &EIdx,
    n: u64,
) -> Result<Option<(NIdx, LsIdx)>, CheckError> {
    if n == 0 {
        if e.tag() == ETAG_CONST {
            match view_const(pers, st, e) {
                None => fail_dangling_e(),
                Some((c, us)) => Ok(Some((c, us))),
            }
        } else {
            Ok(None)
        }
    } else if e.tag() == ETAG_APP {
        match view_app(pers, st, e) {
            None => fail_dangling_e(),
            Some((f, a)) => {
                if a.tag() == ETAG_FVAR {
                    match view_fvar_idx(pers, st, &a) {
                        None => fail_dangling_e(),
                        Some(j) => {
                            if j == b + (n - 1) {
                                ph_app(pers, st, b, &f, n - 1)
                            } else {
                                Ok(None)
                            }
                        }
                    }
                } else {
                    Ok(None)
                }
            }
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1089-1095 nestCanonSub
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCanonSub` — **the
/// canonical whole-application substitution** of the group `names` at the
/// levels `us` over `n` parameters: member `m` to the canonical hole `fvar (n
/// + m)`; `v == us` is interned-list handle equality.
pub fn nest_canon_sub(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    n: u64,
    c: &NIdx,
    v: &LsIdx,
) -> Result<Option<EIdx>, CheckError> {
    if v.eq2(us) {
        match names_find_idx(names, c, 0) {
            None => Ok(None),
            Some(m) => match sort_zero(pers, st) {
                Err(e) => Err(e),
                Ok(s) => match intern_e_fvar(pers, st, n + m, s) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(Some(r)),
                },
            },
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:925-928 Expr.appHole?
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean appHole?` — the hole a
/// whole application is replaced by (`nestCanonSub` at its constant).
pub fn app_hole(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    b: u64,
    n: u64,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match ph_app(pers, st, b, e, n) {
        Err(er) => Err(er),
        Ok(None) => Ok(None),
        Ok(Some((c, v))) => nest_canon_sub(pers, st, names, us, n, &c, &v),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:930-947 Expr.replaceApps
/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:966-1004 Expr.replaceAppsGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceAppsGo` — **the
/// whole-application replacement**, pre-order, at `nestCanonSub names us`: a
/// subterm that is a whole application is replaced by its hole and not
/// descended into; free variables are leaves.  Memoised on the node.
pub fn replace_apps_go(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    b: u64,
    n: u64,
    memo: HashMap<EIdx, EIdx>,
    fuel: u64,
    h: &EIdx,
) -> Result<(EIdx, HashMap<EIdx, EIdx>), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_REPLACE_APPS)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Sort(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Lit(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::FVar(_, _)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Const(_, _)) => match app_hole(pers, st, names, us, b, n, h) {
                Err(e) => Err(e),
                Ok(Some(r)) => Ok((r, memo)),
                Ok(None) => Ok((h.dup2(), memo)),
            },
            Ok(v) => match memo_e_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match replace_apps_node(pers, st, names, us, b, n, memo, fuel - 1, h, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, EIdx> = m;
                        m2.insert(h.dup2(), r.dup2());
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:966-1004 Expr.replaceAppsGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceAppsGo` — the
/// walk's compound arms: an application is a whole application (its hole) or
/// rebuilt from its replaced halves.
pub fn replace_apps_node(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    b: u64,
    n: u64,
    memo: HashMap<EIdx, EIdx>,
    fuel: u64,
    h: &EIdx,
    v: ENodeView,
) -> Result<(EIdx, HashMap<EIdx, EIdx>), CheckError> {
    match v {
        ENodeView::App(a, x) => match app_hole(pers, st, names, us, b, n, h) {
            Err(e) => Err(e),
            Ok(Some(r)) => Ok((r, memo)),
            Ok(None) => replace_apps_app(pers, st, names, us, b, n, memo, fuel, &a, &x),
        },
        ENodeView::Lam(t, body, bm) => match replace_apps_go(pers, st, names, us, b, n, memo, fuel, &t) {
            Err(e) => Err(e),
            Ok((t2, m)) => match replace_apps_go(pers, st, names, us, b, n, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match intern_e_lam(pers, st, t2, b2, bm) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((r, m2)),
                },
            },
        },
        ENodeView::ForallE(t, body, bm) => {
            match replace_apps_go(pers, st, names, us, b, n, memo, fuel, &t) {
                Err(e) => Err(e),
                Ok((t2, m)) => match replace_apps_go(pers, st, names, us, b, n, m, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b2, m2)) => match intern_e_forall_e(pers, st, t2, b2, bm) {
                        Err(e) => Err(e),
                        Ok(r) => Ok((r, m2)),
                    },
                },
            }
        }
        ENodeView::LetE(t, val, body) => match replace_apps_go(pers, st, names, us, b, n, memo, fuel, &t) {
            Err(e) => Err(e),
            Ok((t2, m)) => match replace_apps_go(pers, st, names, us, b, n, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((v2, m2)) => match replace_apps_go(pers, st, names, us, b, n, m2, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b2, m3)) => match intern_e_let_e(pers, st, t2, v2, b2) {
                        Err(e) => Err(e),
                        Ok(r) => Ok((r, m3)),
                    },
                },
            },
        },
        ENodeView::Proj(s, i, x) => match replace_apps_go(pers, st, names, us, b, n, memo, fuel, &x) {
            Err(e) => Err(e),
            Ok((x2, m)) => match intern_e_proj(pers, st, s, i, x2) {
                Err(e) => Err(e),
                Ok(r) => Ok((r, m)),
            },
        },
        _ => Ok((h.dup2(), memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:966-1004 Expr.replaceAppsGo
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceAppsGo` — the
/// application arm's rebuild, split off so the arm ends in a call (extraction
/// rule F3).
pub fn replace_apps_app(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    b: u64,
    n: u64,
    memo: HashMap<EIdx, EIdx>,
    fuel: u64,
    a: &EIdx,
    x: &EIdx,
) -> Result<(EIdx, HashMap<EIdx, EIdx>), CheckError> {
    match replace_apps_go(pers, st, names, us, b, n, memo, fuel, a) {
        Err(e) => Err(e),
        Ok((a2, m)) => match replace_apps_go(pers, st, names, us, b, n, m, fuel, x) {
            Err(e) => Err(e),
            Ok((x2, m2)) => match intern_e_app(pers, st, a2, x2) {
                Err(e) => Err(e),
                Ok(r) => Ok((r, m2)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1077-1079 Expr.replaceAppsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean replaceApps` — the
/// executed `replaceApps` at `nestCanonSub names us n` (one memoised DAG walk).
pub fn replace_apps(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    b: u64,
    n: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match replace_apps_go(pers, st, names, us, b, n, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1086-1087 nestPhs
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestPhs` — the
/// canonical parameter variables `fvar 0, …, fvar (n - 1)` at `Sort 0`.
pub fn nest_phs(pers: &PersTier, st: &mut AState, n: u64, i: u64, out: Vec<EIdx>) -> Result<Vec<EIdx>, CheckError> {
    if i >= n {
        Ok(out)
    } else {
        match sort_zero(pers, st) {
            Err(e) => Err(e),
            Ok(s) => match intern_e_fvar(pers, st, i, s) {
                Err(e) => Err(e),
                Ok(v) => {
                    let mut o: Vec<EIdx> = out;
                    o.push(v);
                    nest_phs(pers, st, n, i + 1, o)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1097-1102 nestCanonCrest
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCanonCrest` — **a
/// stored constructor type, canonically abstracted**: instantiated at the
/// canonical parameter variables, every whole application of a member of
/// `names` at the levels `us` replaced by its canonical hole.
pub fn nest_canon_crest(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    n: u64,
    cty: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match nest_phs(pers, st, n, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(phs) => match inst_pis_with(pers, st, &phs, 0, cty) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(t)) => match replace_apps(pers, st, names, us, 0, n, &t) {
                Err(e) => Err(e),
                Ok(r) => Ok(Some(r)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1104-1108 nestKeyMap
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestKeyMap` — the
/// variable replacement of a key: the canonical parameter variable `i` to
/// `ds[i]`, the canonical hole `|ds| + m` to `holes[m]`.
pub fn nest_key_map(ds: &Vec<EIdx>, holes: &Vec<EIdx>, i: u64) -> Option<EIdx> {
    let n: u64 = ds.len() as u64;
    if i < n {
        eidx_get(ds, i)
    } else {
        eidx_get(holes, i - n)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1110-1116 nestCrest
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCrest` — **a
/// stored constructor type at a key**: its canonical abstraction, then the
/// key's parameters and the frame's holes put in.
pub fn nest_crest(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    holes: &Vec<EIdx>,
    cty: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match nest_canon_crest(pers, st, names, us, ds.len() as u64, cty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(c)) => {
            let f: FvMap = FvMap::KeyMap(env::eidx_vec_dup(ds), env::eidx_vec_dup(holes));
            match replace_fvars(pers, st, &f, &c) {
                Err(e) => Err(e),
                Ok(r) => Ok(Some(r)),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The container's former, and a frame's constructors
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1118-1158 nestInstType
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestInstType` — the
/// `indInfo` lookup of the container, its constant read out.
pub fn ind_cv_of(vis: u64, fe: &IFEnv, c: &NIdx) -> Option<IConstantVal> {
    match env::ifenv_find(vis, fe, c) {
        Some(IConstantInfo::IndInfo(cv, _)) => Some(env::i_constant_val_dup(cv)),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1118-1158 nestInstType
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestInstType` — the
/// instantiation's type former, checked as official checks the auxiliary
/// type before the block exists: the level count, the parameters bound, (N2)
/// the index telescope names no member and no hole below `hi`, (N3) the sort
/// is `Level.isEquiv` the block's.  Returns the index count and the
/// container's type at the key (the type of the frame's hole).
pub fn nest_inst_type(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    ctx: &NestCtx,
    hi: u64,
    key: &NestKey,
) -> Result<(u64, EIdx), CheckError> {
    match checker_base::unwrap_or(
        ind_cv_of(ctx.vis, fe, &key.cname),
        core_types::internal(code_points(&M_VANISHED)),
    ) {
        Err(e) => Err(e),
        Ok(cv_c) => match crate::arena::monad::view_ls_len(pers, st, &key.lvls) {
            None => crate::arena::monad::fail_dangling_ls(),
            Some(nl) => {
                if nl != cv_c.level_params.len() {
                    fail(core_types::invalid(code_points(&M_LEVELS)))
                } else {
                    match expr_ops::strip_pis(pers, st, key.ds.len() as u64, &cv_c.ty) {
                        Err(e) => Err(e),
                        Ok(None) => fail(core_types::invalid(code_points(&M_NO_PARAMS))),
                        Ok(Some(_)) => nest_inst_type_at(pers, st, ctx, hi, key, &cv_c),
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1118-1158 nestInstType
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestInstType` — the
/// instantiated type, its telescope and its sort.
pub fn nest_inst_type_at(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    hi: u64,
    key: &NestKey,
    cv_c: &IConstantVal,
) -> Result<(u64, EIdx), CheckError> {
    match expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv_c.level_params, &key.lvls, &cv_c.ty) {
        Err(e) => Err(e),
        Ok(tl) => match inst_pis_with(pers, st, &key.ds, 0, &tl) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::invalid(code_points(&M_NO_PARAMS))),
            Ok(Some(ty)) => match pi_binders(pers, st, CORE_WALK_FUEL, &ty, Vec::new()) {
                Err(e) => Err(e),
                Ok((bs, res)) => match view(pers, st, &res) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Sort(s)) => nest_inst_type_sort(pers, st, ctx, hi, bs, s, ty),
                    Ok(_) => fail(core_types::invalid(code_points(&M_NOT_SORT))),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1118-1158 nestInstType
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestInstType` — (N2)
/// and (N3).
#[allow(clippy::too_many_arguments)]
pub fn nest_inst_type_sort(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    hi: u64,
    bs: Vec<(EIdx, BinderMeta)>,
    s: LIdx,
    ty: EIdx,
) -> Result<(u64, EIdx), CheckError> {
    match nest_occ_any_binder(pers, st, &ctx.names, ctx.n_p, hi, &bs, 0) {
        Err(e) => Err(e),
        Ok(true) => fail(core_types::invalid(code_points(&M_IDX_MENTIONS))),
        Ok(false) => match core::lvl_eq(pers, st, &s, &ctx.sort) {
            Err(e) => Err(e),
            Ok(o) => match core::lift_fueled(o) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::invalid(code_points(&M_UNIVERSE))),
                Ok(true) => Ok((bs.len() as u64, ty)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1160-1167 nestResHead
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestResHead` — a
/// constructor's result is headed by a variable (its hole).
pub fn nest_res_head(pers: &PersTier, st: &AState, e: &EIdx) -> Result<bool, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(hd) => Ok(hd.tag() == ETAG_FVAR),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1169-1186 nestFields
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFields` — a
/// constructor's field telescope `cur` (`nF` fields from field `j`), each
/// field through the walk at its depth `base + j`, the field opened at the
/// variable `base + j` (annotated by its DECLARED domain): the fields' kinds,
/// their walked forms, and the result.  Lean conses on the way out; the port
/// pushes on the way in, which is the same order of effects.
#[allow(clippy::too_many_arguments)]
pub fn nest_fields(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    base: u64,
    n_f: u64,
    j: u64,
    cur: &EIdx,
    ns: NestState,
    ks: Vec<NestFieldKind>,
    nds: Vec<(EIdx, BinderMeta)>,
) -> Result<(Vec<NestFieldKind>, Vec<(EIdx, BinderMeta)>, EIdx, NestState), CheckError> {
    if n_f == 0 {
        Ok((ks, nds, cur.dup2(), ns))
    } else if cur.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, cur) {
            None => fail_dangling_e(),
            Some((a, b, bm)) => {
                match nest_pos(pers, st, mode, fe, ctx, fuel, prog, base + j, 0, &a, ns) {
                    Err(e) => Err(e),
                    Ok((k, nd, ns2)) => match intern_e_fvar(pers, st, base + j, a.dup2()) {
                        Err(e) => Err(e),
                        Ok(fv) => match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &b, &fv, 0) {
                            Err(e) => Err(e),
                            Ok(b2) => {
                                let mut ks2: Vec<NestFieldKind> = ks;
                                ks2.push(k);
                                let mut nds2: Vec<(EIdx, BinderMeta)> = nds;
                                nds2.push((nd, bm));
                                nest_fields(
                                    pers, st, mode, fe, ctx, fuel, prog, base, n_f - 1, j + 1, &b2,
                                    ns2, ks2, nds2,
                                )
                            }
                        },
                    },
                }
            }
        }
    } else {
        fail(core_types::invalid(code_points(&M_CTOR_FIELDS)))
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1188-1196 nestCtorNf
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtorNf` — **a
/// frame constructor's record** (K.53′): the constructor at the frame's key
/// `(us, ds)` under the frames `prog`, its walked telescope `closed`
/// (con-leche's `closeTelescope nds hi cur`, computed once by the caller),
/// all read back.
#[allow(clippy::too_many_arguments)]
pub fn nest_ctor_nf(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    prog: &Vec<NestHole>,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    cv: &IConstantVal,
    closed: &EIdx,
) -> Result<NestCtorNf, CheckError> {
    let f: FvMap = FvMap::HoleImg(HoleImgMap {
        ctx: nest_ctx_dup(ctx),
        prog: nest_holes_dup(prog, 0, Vec::new()),
        n: prog.len() as u64,
    });
    match replace_fvars_list(pers, st, &f, ds, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(ds2) => match replace_fvars(pers, st, &f, closed) {
            Err(e) => Err(e),
            Ok(ty) => Ok(NestCtorNf {
                ctor: cv.name.dup2(),
                lvls: us.dup2(),
                ds: ds2,
                ty,
            }),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtors` — U4: some
/// field `i ≥ i0` that is not ordinary is read by a later field or by the
/// result (`structUsedLater` on the walked telescope; the kind is tested
/// first, as the cited `&&` does).
pub fn nest_u4(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<NestFieldKind>,
    closed: &EIdx,
    n_f: u64,
    i: u64,
) -> Result<bool, CheckError> {
    if i >= n_f {
        Ok(false)
    } else {
        let ordinary: bool = if i < ks.len() as u64 {
            nest_field_kind_is_ordinary(&ks[i as usize])
        } else {
            true
        };
        if ordinary {
            nest_u4(pers, st, ks, closed, n_f, i + 1)
        } else {
            match struct_parts::struct_used_later(pers, st, closed, 0, i) {
                Err(e) => Err(e),
                Ok(true) => Ok(true),
                Ok(false) => nest_u4(pers, st, ks, closed, n_f, i + 1),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtors` — **a
/// frame's constructors**, the root frame's (`root`: each constructor walked
/// at the input-derived fuel of its instantiated type) and every container
/// frame's (at the enclosing walk's `fuel`) alike: each with the frame's
/// group abstracted (`nestCrest`), TYPED at the frame's context, its fields
/// walked above `hi`, U4, its result indices hole-free, and its walked normal
/// form recorded.  Returns every constructor's kinds and walked form, in
/// order.
#[allow(clippy::too_many_arguments)]
pub fn nest_ctors(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    root: bool,
    fuel: u64,
    prog: &Vec<NestHole>,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    names: &Vec<NIdx>,
    holes: &Vec<EIdx>,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    ns: NestState,
    outs: Vec<(Vec<NestFieldKind>, EIdx)>,
) -> Result<(Vec<(Vec<NestFieldKind>, EIdx)>, NestState), CheckError> {
    if i >= cs.len() {
        Ok((outs, ns))
    } else {
        let cv: IConstantVal = env::i_constant_val_dup(&cs[i].0);
        let n_f: u64 = cs[i].1;
        if !checker_base::name_nodup(&cv.level_params) {
            fail(core_types::invalid(code_points(&M_DUP_ULP)))
        } else {
            match expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv.level_params, us, &cv.ty) {
                Err(e) => Err(e),
                Ok(cty) => match nest_crest(pers, st, names, us, ds, holes, &cty) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::invalid(code_points(&M_CTOR_PARAMS))),
                    Ok(Some(crest)) => nest_ctors_typed(
                        pers, st, mode, fe, ctx, root, fuel, prog, hi, us, ds, names, holes, cs, i, ns,
                        outs, cv, n_f, crest,
                    ),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtors` — the
/// crest typed at the frame's context, and its fields walked.
#[allow(clippy::too_many_arguments)]
pub fn nest_ctors_typed(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    root: bool,
    fuel: u64,
    prog: &Vec<NestHole>,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    names: &Vec<NIdx>,
    holes: &Vec<EIdx>,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    ns: NestState,
    outs: Vec<(Vec<NestFieldKind>, EIdx)>,
    cv: IConstantVal,
    n_f: u64,
    crest: EIdx,
) -> Result<(Vec<(Vec<NestFieldKind>, EIdx)>, NestState), CheckError> {
    match core::infer_type_core(pers, ctx.vis, st, mode, fe, core::CHECK_FUEL, hi, &crest) {
        Err(e) => Err(e),
        Ok(ty) => match core::ensure_sort_core(pers, ctx.vis, st, mode, fe, core::CHECK_FUEL, hi, &ty) {
            Err(e) => Err(e),
            Ok(_) => {
                if root {
                    match whnf_walk_fuel(pers, st, &crest) {
                        Err(e) => Err(e),
                        Ok(fuel_c) => nest_ctors_walk(
                            pers, st, mode, fe, ctx, root, fuel, prog, hi, us, ds, names, holes, cs, i, ns,
                            outs, cv, n_f, crest, fuel_c,
                        ),
                    }
                } else {
                    nest_ctors_walk(
                        pers, st, mode, fe, ctx, root, fuel, prog, hi, us, ds, names, holes, cs, i, ns, outs,
                        cv, n_f, crest, fuel,
                    )
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtors` — the
/// fields walked at the constructor's fuel `fuel_c` (`rec crest`: the root's
/// input-derived one, a frame's enclosing one).  Its own function so the two
/// fuels are two tail calls (extraction rule F2).
#[allow(clippy::too_many_arguments)]
pub fn nest_ctors_walk(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    root: bool,
    fuel: u64,
    prog: &Vec<NestHole>,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    names: &Vec<NIdx>,
    holes: &Vec<EIdx>,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    ns: NestState,
    outs: Vec<(Vec<NestFieldKind>, EIdx)>,
    cv: IConstantVal,
    n_f: u64,
    crest: EIdx,
    fuel_c: u64,
) -> Result<(Vec<(Vec<NestFieldKind>, EIdx)>, NestState), CheckError> {
    match nest_fields(pers, st, mode, fe, ctx, fuel_c, prog, hi, n_f, 0, &crest, ns, Vec::new(), Vec::new()) {
        Err(e) => Err(e),
        Ok((ks, nds, cur, ns2)) => nest_ctors_done(
            pers, st, mode, fe, ctx, root, fuel, prog, hi, us, ds, names, holes, cs, i, ns2, outs, cv, n_f,
            ks, nds, cur,
        ),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtors` — U4, the
/// result's head and indices, the normal form recorded, and the rest of the
/// constructors.
#[allow(clippy::too_many_arguments)]
pub fn nest_ctors_done(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    root: bool,
    fuel: u64,
    prog: &Vec<NestHole>,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    names: &Vec<NIdx>,
    holes: &Vec<EIdx>,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    ns: NestState,
    outs: Vec<(Vec<NestFieldKind>, EIdx)>,
    cv: IConstantVal,
    n_f: u64,
    ks: Vec<NestFieldKind>,
    nds: Vec<(EIdx, BinderMeta)>,
    cur: EIdx,
) -> Result<(Vec<(Vec<NestFieldKind>, EIdx)>, NestState), CheckError> {
    match close_telescope(pers, st, &nds, 0, hi, &cur) {
        Err(e) => Err(e),
        Ok(closed) => match nest_u4(pers, st, &ks, &closed, n_f, 0) {
            Err(e) => Err(e),
            Ok(true) => fail(core_types::invalid(code_points(&M_U4))),
            Ok(false) => match nest_res_ok(pers, st, ctx, hi, &cur) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::invalid(code_points(&M_RET))),
                Ok(true) => match nest_ctor_nf(pers, st, ctx, prog, us, ds, &cv, &closed) {
                    Err(e) => Err(e),
                    Ok(nf) => {
                        let mut ns2: NestState = ns;
                        ns2.ctor_nfs.push(nf);
                        let mut outs2: Vec<(Vec<NestFieldKind>, EIdx)> = outs;
                        outs2.push((ks, closed));
                        nest_ctors(
                            pers, st, mode, fe, ctx, root, fuel, prog, hi, us, ds, names, holes, cs, i + 1,
                            ns2, outs2,
                        )
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCtors` —
/// official's "invalid return type" on the instantiated constructor: its
/// result is headed by its hole and its indices are hole-free below `hi` (the
/// head tested first, as the cited `&&` does).
pub fn nest_res_ok(
    pers: &PersTier,
    st: &AState,
    ctx: &NestCtx,
    hi: u64,
    cur: &EIdx,
) -> Result<bool, CheckError> {
    match nest_res_head(pers, st, cur) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, cur) {
            Err(e) => Err(e),
            Ok(args) => match nest_occ_any(pers, st, &ctx.names, ctx.n_p, hi, &args, 0) {
                Err(e) => Err(e),
                Ok(occ) => {
                    if occ {
                        Ok(false)
                    } else {
                        Ok(true)
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// A container frame
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1264-1276 nestGroupCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestGroupCtors` — the
/// constructors of every container in `cs[i..]` (at one parameter count),
/// looked up; `ctors ++ rest` with the head's effects first.
#[allow(clippy::too_many_arguments)]
pub fn nest_group_ctors(
    pers: &PersTier,
    st: &AState,
    fe: &IFEnv,
    ctx: &NestCtx,
    n_pc: u64,
    cs: &Vec<NIdx>,
    i: usize,
    out: Vec<(IConstantVal, u64)>,
) -> Result<Vec<(IConstantVal, u64)>, CheckError> {
    if i >= cs.len() {
        Ok(out)
    } else {
        match nest_container(pers, st, ctx.vis, fe, &cs[i]) {
            Err(e) => Err(e),
            Ok(None) => fail(nest_non_valid()),
            Ok(Some((n_pc2, ctors))) => {
                if !(n_pc2 == n_pc || ctors.len() == 0) {
                    fail(core_types::invalid(code_points(&M_GROUP_PARAMS)))
                } else {
                    let o: Vec<(IConstantVal, u64)> = ctor_pairs_append(out, &ctors, 0);
                    nest_group_ctors(pers, st, fe, ctx, n_pc, cs, i + 1, o)
                }
            }
        }
    }
}

/// con-leche: none — `xs ++ ys` over a constructor list
/// Lean twin: `ctors ++ rest`.
pub fn ctor_pairs_append(
    xs: Vec<(IConstantVal, u64)>,
    ys: &Vec<(IConstantVal, u64)>,
    i: usize,
) -> Vec<(IConstantVal, u64)> {
    if i >= ys.len() {
        xs
    } else {
        let mut o: Vec<(IConstantVal, u64)> = xs;
        o.push((env::i_constant_val_dup(&ys[i].0), ys[i].1));
        ctor_pairs_append(o, ys, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1278-1283 nestBlockOf
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestBlockOf` — the
/// recorded block of the inductive `C` (`IndCaps.all`): `[]` when none is
/// recorded.
pub fn nest_block_of(ctx: &NestCtx, fe: &IFEnv, c: &NIdx) -> Vec<NIdx> {
    match env::ifenv_find(ctx.vis, fe, c) {
        Some(IConstantInfo::IndInfo(_, caps)) => env::nidx_vec_dup(&caps.all),
        _ => Vec::new(),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1285-1291 nestFrameMates
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFrameMates` — the
/// cited `eraseDups` (first occurrences, in order) and the `filter (· != C)`,
/// in one index recursion.
pub fn frame_mates_from(ns: &Vec<NIdx>, c: &NIdx, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= ns.len() {
        out
    } else if ns[i].eq2(c) || names_contain(&out, &ns[i], 0) {
        frame_mates_from(ns, c, i + 1, out)
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(ns[i].dup2());
        frame_mates_from(ns, c, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1285-1291 nestFrameMates
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFrameMates` — **a
/// frame's group-mates** (N2-eager): every OTHER member of the container `C`'s
/// recorded block, each once.  (`eraseDups` then `filter` keeps the first
/// occurrence of every name that is not `C`, which is what the one pass
/// keeps.)
pub fn nest_frame_mates(ctx: &NestCtx, fe: &IFEnv, c: &NIdx) -> Vec<NIdx> {
    let all: Vec<NIdx> = nest_block_of(ctx, fe, c);
    frame_mates_from(&all, c, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1293-1307 nestArity
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestArity` — **a frame
/// hole's full arity**: its container member's recorded type's binder count.
pub fn nest_arity(
    pers: &PersTier,
    st: &AState,
    ctx: &NestCtx,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<u64, CheckError> {
    match ind_cv_of(ctx.vis, fe, c) {
        None => Ok(0),
        Some(cv) => match pi_binders(pers, st, CORE_WALK_FUEL, &cv.ty, Vec::new()) {
            Err(e) => Err(e),
            Ok((bs, _)) => Ok(bs.len() as u64),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1309-1316 nestGrowGroup
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestGrowGroup` — a
/// frame's group grown by the named containers, each at the frame's
/// instantiation, its hole typed by its instantiated former.
#[allow(clippy::too_many_arguments)]
pub fn nest_grow_group(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    ctx: &NestCtx,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    cs: &Vec<NIdx>,
    i: usize,
    grp: Vec<(NIdx, EIdx)>,
) -> Result<Vec<(NIdx, EIdx)>, CheckError> {
    if i >= cs.len() {
        Ok(grp)
    } else {
        let key: NestKey = NestKey {
            cname: cs[i].dup2(),
            lvls: us.dup2(),
            ds: env::eidx_vec_dup(ds),
        };
        match nest_inst_type(pers, st, fe, ctx, hi, &key) {
            Err(e) => Err(e),
            Ok((_, cty)) => {
                let mut g: Vec<(NIdx, EIdx)> = grp;
                g.push((cs[i].dup2(), cty));
                nest_grow_group(pers, st, fe, ctx, hi, us, ds, cs, i + 1, g)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1318-1325 nestAcceptGroup
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestAcceptGroup` — a
/// frame's group accepted with its instantiation: every member at `(us, ds)`
/// cached, those not cached yet.
pub fn nest_accept_group(
    us: &LsIdx,
    ds: &Vec<EIdx>,
    grp: &Vec<(NIdx, EIdx)>,
    i: usize,
    keys: Vec<NestKey>,
) -> Vec<NestKey> {
    if i >= grp.len() {
        keys
    } else {
        let k: NestKey = NestKey {
            cname: grp[i].0.dup2(),
            lvls: us.dup2(),
            ds: env::eidx_vec_dup(ds),
        };
        if nest_keys_contain(&keys, &k, 0) {
            nest_accept_group(us, ds, grp, i + 1, keys)
        } else {
            let mut ks: Vec<NestKey> = keys;
            ks.push(k);
            nest_accept_group(us, ds, grp, i + 1, ks)
        }
    }
}

/// con-leche: none — `grp.map (·.1)`
/// Lean twin: `grp.map (·.1)`.
pub fn group_names(grp: &Vec<(NIdx, EIdx)>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= grp.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(grp[i].0.dup2());
        group_names(grp, i + 1, o)
    }
}

/// con-leche: none — `grp.map fun (c, _) => ({ key := ⟨c, us, ds⟩, … } : NestKey)`
/// Lean twin: the group's keys, in order.
pub fn group_keys(
    us: &LsIdx,
    ds: &Vec<EIdx>,
    grp: &Vec<(NIdx, EIdx)>,
    i: usize,
    out: Vec<NestKey>,
) -> Vec<NestKey> {
    if i >= grp.len() {
        out
    } else {
        let mut o: Vec<NestKey> = out;
        o.push(NestKey {
            cname: grp[i].0.dup2(),
            lvls: us.dup2(),
            ds: env::eidx_vec_dup(ds),
        });
        group_keys(us, ds, grp, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFrame` —
/// `(grp.mapIdx fun _ (c, _) => { key := ⟨c, us, ds⟩, base := hi }).reverse ++
/// prog`, which over the outermost-first `Vec` is `prog` followed by the
/// group's holes in order (the module note).
pub fn frame_stack(
    prog: &Vec<NestHole>,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    hi: u64,
    grp: &Vec<(NIdx, EIdx)>,
    i: usize,
    out: Vec<NestHole>,
) -> Vec<NestHole> {
    if i >= grp.len() {
        out
    } else {
        let mut o: Vec<NestHole> = out;
        o.push(NestHole {
            key: NestKey {
                cname: grp[i].0.dup2(),
                lvls: us.dup2(),
                ds: env::eidx_vec_dup(ds),
            },
            base: hi,
        });
        frame_stack(prog, us, ds, hi, grp, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFrame` —
/// `grp.mapIdx fun i (_, ty) => Expr.fvar (hi + i) ty`: the frame's holes.
pub fn frame_holes(
    pers: &PersTier,
    st: &mut AState,
    hi: u64,
    grp: &Vec<(NIdx, EIdx)>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= grp.len() {
        Ok(out)
    } else {
        match intern_e_fvar(pers, st, hi + (i as u64), grp[i].1.dup2()) {
            Err(e) => Err(e),
            Ok(v) => {
                let mut o: Vec<EIdx> = out;
                o.push(v);
                frame_holes(pers, st, hi, grp, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFrame` — **a
/// container frame** at the instantiation `(us, ds)`: the instantiation TYPED
/// at the frame's depth (K.52), its holes the container's WHOLE recorded
/// group `grp`, every one of their constructors walked with all of them
/// abstracted, in one pass (N2-eager).  `grp` is never empty (it starts at the
/// instantiation met); the cited `grp.headD default` falls back to the
/// anonymous name, which the port interns.
#[allow(clippy::too_many_arguments)]
pub fn nest_frame(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    n_pc: u64,
    grp: &Vec<(NIdx, EIdx)>,
    ns: NestState,
) -> Result<NestState, CheckError> {
    if grp.len() == 0 {
        match intern_n_node(pers, st, NNodeView::Anonymous) {
            Err(e) => Err(e),
            Ok(hn) => nest_frame_at(pers, st, mode, fe, ctx, fuel, prog, hi, us, ds, n_pc, grp, ns, hn),
        }
    } else {
        let hn: NIdx = grp[0].0.dup2();
        nest_frame_at(pers, st, mode, fe, ctx, fuel, prog, hi, us, ds, n_pc, grp, ns, hn)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFrame` — K.52:
/// the instantiation `hn.{us} ds` typed at the frame's own depth, then the
/// walk.
#[allow(clippy::too_many_arguments)]
pub fn nest_frame_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    n_pc: u64,
    grp: &Vec<(NIdx, EIdx)>,
    ns: NestState,
    hn: NIdx,
) -> Result<NestState, CheckError> {
    match intern_e_const(pers, st, hn, us.dup2()) {
        Err(e) => Err(e),
        Ok(hc) => match expr_ops::mk_app_n(pers, st, &hc, ds) {
            Err(e) => Err(e),
            Ok(app) => match core::infer_type_core(pers, ctx.vis, st, mode, fe, core::CHECK_FUEL, hi, &app) {
                Err(e) => Err(e),
                Ok(_) => nest_frame_walk(pers, st, mode, fe, ctx, fuel, prog, hi, us, ds, n_pc, grp, ns),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestFrame` — the
/// frame's stack, its group's constructors and the one walk over them.
#[allow(clippy::too_many_arguments)]
pub fn nest_frame_walk(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    hi: u64,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    n_pc: u64,
    grp: &Vec<(NIdx, EIdx)>,
    ns: NestState,
) -> Result<NestState, CheckError> {
    let prog2: Vec<NestHole> = frame_stack(prog, us, ds, hi, grp, 0, nest_holes_dup(prog, 0, Vec::new()));
    let names: Vec<NIdx> = group_names(grp, 0, Vec::new());
    match nest_group_ctors(pers, st, fe, ctx, n_pc, &names, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(ctors) => match frame_holes(pers, st, hi, grp, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(holes) => match nest_ctors(
                pers,
                st,
                mode,
                fe,
                ctx,
                false,
                fuel,
                &prog2,
                hi + (grp.len() as u64),
                us,
                ds,
                &names,
                &holes,
                &ctors,
                0,
                ns,
                Vec::new(),
            ) {
                Err(e) => Err(e),
                Ok((_, ns2)) => Ok(ns2),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1353-1357 nestWalkStack
/// Lean twin: `ds.all (fun x => x.fvarB ≤ bound)` — the cited closedness test of
/// an instantiation's parameters, in order, stopping at the first failure.
pub fn all_fvar_b_le(
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<EIdx>,
    bound: u64,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ds.len() {
        Ok(true)
    } else {
        let x: EIdx = ds[i].dup2();
        match expr_ops::fvar_b(pers, st, CORE_WALK_FUEL, &x) {
            Err(e) => Err(e),
            Ok(b) => {
                if b <= bound {
                    all_fvar_b_le(pers, st, ds, bound, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1353-1357 nestWalkStack
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestWalkStack` — **the
/// frame stack an instantiation is walked under**: the EMPTY one when its
/// parameters mention no frame hole, else the frames it was met under.
pub fn nest_walk_stack(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    prog: &Vec<NestHole>,
    ds: &Vec<EIdx>,
) -> Result<Vec<NestHole>, CheckError> {
    match all_fvar_b_le(pers, st, ds, hi_at(ctx, 0), 0) {
        Err(e) => Err(e),
        Ok(true) => Ok(Vec::new()),
        Ok(false) => Ok(nest_holes_dup(prog, 0, Vec::new())),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1359-1382 nestContNew
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestContNew` — an
/// instantiation's frame: the group-mates' former checks, the frame walked
/// with the whole group in progress, and the whole group cached when its
/// parameters mention no frame hole.
#[allow(clippy::too_many_arguments)]
pub fn nest_cont_new(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    kb: u64,
    n: &NIdx,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    n_pc: u64,
    cty: &EIdx,
    ns: NestState,
) -> Result<(NestFieldKind, NestState), CheckError> {
    match nest_walk_stack(pers, st, ctx, prog, ds) {
        Err(e) => Err(e),
        Ok(wp) => {
            let mates: Vec<NIdx> = nest_frame_mates(ctx, fe, n);
            let mut grp0: Vec<(NIdx, EIdx)> = Vec::new();
            grp0.push((n.dup2(), cty.dup2()));
            let hw: u64 = hi_at(ctx, wp.len() as u64);
            match nest_grow_group(pers, st, fe, ctx, hw, us, ds, &mates, 0, grp0) {
                Err(e) => Err(e),
                Ok(grp) => {
                    let act: Vec<NestKey> = nest_keys_dup(&ns.active, 0, Vec::new());
                    let active: Vec<NestKey> = nest_keys_dup(&ns.active, 0, group_keys(us, ds, &grp, 0, Vec::new()));
                    let ns1: NestState = NestState {
                        keys: ns.keys,
                        active,
                        ctor_nfs: ns.ctor_nfs,
                    };
                    match nest_frame(pers, st, mode, fe, ctx, fuel, &wp, hw, us, ds, n_pc, &grp, ns1) {
                        Err(e) => Err(e),
                        Ok(ns2) => match all_fvar_b_le(pers, st, ds, hi_at(ctx, 0), 0) {
                            Err(e) => Err(e),
                            Ok(closed) => {
                                let keys: Vec<NestKey> = if closed {
                                    nest_accept_group(us, ds, &grp, 0, ns2.keys)
                                } else {
                                    ns2.keys
                                };
                                Ok((
                                    NestFieldKind::Nested(kb != 0),
                                    NestState {
                                        keys,
                                        active: act,
                                        ctor_nfs: ns2.ctor_nfs,
                                    },
                                ))
                            }
                        },
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1384-1404 nestContKey
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestContKey` — the
/// instantiation `(n, us, ds)` met: IN PROGRESS (met as a constant, which only
/// reduction produces: official's "non valid occurrence"); cached — a hit,
/// but only when its parameters mention no frame hole; else a new frame.
#[allow(clippy::too_many_arguments)]
pub fn nest_cont_key(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    kb: u64,
    n: &NIdx,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    n_pc: u64,
    cty: &EIdx,
    ns: NestState,
) -> Result<(NestFieldKind, NestState), CheckError> {
    let key: NestKey = NestKey {
        cname: n.dup2(),
        lvls: us.dup2(),
        ds: env::eidx_vec_dup(ds),
    };
    if nest_keys_contain(&ns.active, &key, 0) {
        fail(core_types::invalid(code_points(&M_IN_PROGRESS)))
    } else {
        match all_fvar_b_le(pers, st, ds, hi_at(ctx, 0), 0) {
            Err(e) => Err(e),
            Ok(closed) => {
                if closed && nest_keys_contain(&ns.keys, &key, 0) {
                    Ok((NestFieldKind::Nested(kb != 0), ns))
                } else {
                    nest_cont_new(pers, st, mode, fe, ctx, fuel, prog, kb, n, us, ds, n_pc, cty, ns)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1406-1440 nestCont
/// Lean twin: `(args.drop q.1).all (!·.nestOcc names nP hi)` and
/// `(args.take q.1).all (fun x => x.bvarB == 0 && x.fvarB ≤ hi)` — the second
/// test, in order, the `bvarB` read first.
pub fn params_closed(
    pers: &PersTier,
    st: &mut AState,
    xs: &Vec<EIdx>,
    hi: u64,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= xs.len() {
        Ok(true)
    } else {
        let x: EIdx = xs[i].dup2();
        match expr_ops::bvar_b(pers, st, CORE_WALK_FUEL, &x) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb != 0 {
                    Ok(false)
                } else {
                    match expr_ops::fvar_b(pers, st, CORE_WALK_FUEL, &x) {
                        Err(e) => Err(e),
                        Ok(fb) => {
                            if fb <= hi {
                                params_closed(pers, st, xs, hi, i + 1)
                            } else {
                                Ok(false)
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1406-1440 nestCont
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCont` — **the
/// container case** of `nestPos`: the reduct is the stored inductive `n.{us}`
/// applied to `args`; its constructors looked up (`nestContainer`), its checks
/// (enough arguments and hole-free indices, not `Quot`, parameters without
/// local variables), the instantiation's former (`nestInstType`), full
/// application; then the instantiation (`nestContKey`).  `fuel` is the walk's
/// own, one lower.
#[allow(clippy::too_many_arguments)]
pub fn nest_cont(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    kb: u64,
    n: &NIdx,
    us: &LsIdx,
    args: &Vec<EIdx>,
    ns: NestState,
) -> Result<(NestFieldKind, NestState), CheckError> {
    match nest_container(pers, st, ctx.vis, fe, n) {
        Err(e) => Err(e),
        Ok(None) => fail(nest_non_valid()),
        Ok(Some((n_pc, _))) => {
            let hp: u64 = hi_at(ctx, prog.len() as u64);
            if (args.len() as u64) < n_pc {
                fail(nest_non_valid())
            } else {
                let idx: Vec<EIdx> = core::drop_eidx_n(args, n_pc);
                match nest_occ_any(pers, st, &ctx.names, ctx.n_p, hp, &idx, 0) {
                    Err(e) => Err(e),
                    Ok(true) => fail(nest_non_valid()),
                    Ok(false) => match pin_quot(st) {
                        Err(e) => Err(e),
                        Ok(q) => {
                            if n.eq2(&q) {
                                fail(nest_non_valid())
                            } else {
                                nest_cont_params(pers, st, mode, fe, ctx, fuel, prog, kb, n, us, args, n_pc, ns)
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1406-1440 nestCont
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestCont` — the
/// parameters' closedness, the instantiation's former and the full
/// application, then `nestContKey`.
#[allow(clippy::too_many_arguments)]
pub fn nest_cont_params(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    kb: u64,
    n: &NIdx,
    us: &LsIdx,
    args: &Vec<EIdx>,
    n_pc: u64,
    ns: NestState,
) -> Result<(NestFieldKind, NestState), CheckError> {
    let hp: u64 = hi_at(ctx, prog.len() as u64);
    let ds: Vec<EIdx> = expr_ops::take_eidx_n(args, n_pc);
    match params_closed(pers, st, &ds, hp, 0) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_LOCAL_VARS))),
        Ok(true) => {
            let key: NestKey = NestKey {
                cname: n.dup2(),
                lvls: us.dup2(),
                ds: env::eidx_vec_dup(&ds),
            };
            match nest_inst_type(pers, st, fe, ctx, hp, &key) {
                Err(e) => Err(e),
                Ok((n_i, cty)) => {
                    if args.len() as u64 != n_pc + n_i {
                        fail(core_types::invalid(code_points(&M_NOT_FULL)))
                    } else {
                        nest_cont_key(pers, st, mode, fe, ctx, fuel, prog, kb, n, us, &ds, n_pc, &cty, ns)
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The positivity function
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1442-1496 nestPos
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestPos` — **the
/// positivity function**: the domain `e` at depth `dep`, `kb` `Π` binders
/// into the field, `prog` the instantiations in progress.  The reduct (the
/// kernel's own whnf) mentions no member and no hole — ordinary, its normal
/// form the input unless the input mentions one — or it goes to `nest_pos_at`.
/// Running out of fuel DECLINES.
#[allow(clippy::too_many_arguments)]
pub fn nest_pos(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    dep: u64,
    kb: u64,
    e: &EIdx,
    ns: NestState,
) -> Result<(NestFieldKind, EIdx, NestState), CheckError> {
    if fuel == 0 {
        fail(core_types::not_implemented(code_points(&M_FUEL)))
    } else {
        let hi: u64 = hi_at(ctx, prog.len() as u64);
        match core::whnf(pers, ctx.vis, st, mode, fe, core::CHECK_FUEL, dep, e) {
            Err(er) => Err(er),
            Ok(w) => match nest_occ(pers, st, &ctx.names, ctx.n_p, hi, &w) {
                Err(er) => Err(er),
                Ok(false) => match nest_occ(pers, st, &ctx.names, ctx.n_p, hi, e) {
                    Err(er) => Err(er),
                    Ok(true) => Ok((NestFieldKind::Ordinary, w, ns)),
                    Ok(false) => Ok((NestFieldKind::Ordinary, e.dup2(), ns)),
                },
                Ok(true) => nest_pos_at(pers, st, mode, fe, ctx, fuel - 1, prog, dep, kb, hi, &w, ns),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1442-1496 nestPos
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestPos` — the reduct
/// `w` mentions a member or a hole: a `Π` whose domain is hole-free (`pi`, the
/// codomain walked one binder in), a hole application (`holeApp`), a stored
/// inductive's application (`contApp`), or official's "non valid occurrence".
#[allow(clippy::too_many_arguments)]
pub fn nest_pos_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    fuel: u64,
    prog: &Vec<NestHole>,
    dep: u64,
    kb: u64,
    hi: u64,
    w: &EIdx,
    ns: NestState,
) -> Result<(NestFieldKind, EIdx, NestState), CheckError> {
    if w.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, w) {
            None => fail_dangling_e(),
            Some((a, b, bm)) => match nest_occ(pers, st, &ctx.names, ctx.n_p, hi, &a) {
                Err(er) => Err(er),
                Ok(true) => fail(core_types::invalid(code_points(&M_NON_POSITIVE))),
                Ok(false) => match intern_e_fvar(pers, st, dep, a.dup2()) {
                    Err(er) => Err(er),
                    Ok(fv) => match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &b, &fv, 0) {
                        Err(er) => Err(er),
                        Ok(b2) => match nest_pos(pers, st, mode, fe, ctx, fuel, prog, dep + 1, kb + 1, &b2, ns) {
                            Err(er) => Err(er),
                            Ok((k, nb, ns2)) => match expr_ops::abstract1_fast(pers, st, CORE_WALK_FUEL, &nb, dep, 0) {
                                Err(er) => Err(er),
                                Ok(nb2) => match intern_e_forall_e(pers, st, a, nb2, bm) {
                                    Err(er) => Err(er),
                                    Ok(r) => Ok((k, r, ns2)),
                                },
                            },
                        },
                    },
                },
            },
        }
    } else {
        match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, w) {
            Err(er) => Err(er),
            Ok(args) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, w) {
                Err(er) => Err(er),
                Ok(hd) => match view(pers, st, &hd) {
                    Err(er) => Err(er),
                    Ok(ENodeView::FVar(i, _)) => nest_pos_hole(pers, st, fe, ctx, prog, kb, hi, i, &args, w, ns),
                    Ok(ENodeView::Const(n, us)) => {
                        if names_contain(&ctx.names, &n, 0) {
                            fail(nest_non_valid())
                        } else {
                            match nest_cont(pers, st, mode, fe, ctx, fuel, prog, kb, &n, &us, &args, ns) {
                                Err(er) => Err(er),
                                Ok((k, ns2)) => Ok((k, w.dup2(), ns2)),
                            }
                        }
                    }
                    Ok(_) => fail(nest_non_valid()),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1442-1496 nestPos
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestPos` — the
/// `holeApp` case: a hole standing for its entry's whole application to the
/// parameters, applied to hole-free indices, at its full arity (official
/// `is_valid_ind_app`): a member hole is recursive (or reflexive under `Π`
/// binders), a frame hole an instantiation in progress.
#[allow(clippy::too_many_arguments)]
pub fn nest_pos_hole(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    ctx: &NestCtx,
    prog: &Vec<NestHole>,
    kb: u64,
    hi: u64,
    i: u64,
    args: &Vec<EIdx>,
    w: &EIdx,
    ns: NestState,
) -> Result<(NestFieldKind, EIdx, NestState), CheckError> {
    match nest_hole_at(ctx, prog, i) {
        None => fail(nest_non_valid()),
        Some(h) => match nest_occ_any(pers, st, &ctx.names, ctx.n_p, hi, args, 0) {
            Err(e) => Err(e),
            Ok(true) => fail(nest_non_valid()),
            Ok(false) => match nest_arity(pers, st, ctx, fe, &h.key.cname) {
                Err(e) => Err(e),
                Ok(ar) => {
                    if (args.len() as u64) + (h.key.ds.len() as u64) == ar {
                        let k: NestFieldKind = if i < hi_at(ctx, 0) {
                            if kb == 0 {
                                NestFieldKind::Recursive(i - ctx.n_p)
                            } else {
                                NestFieldKind::Reflexive(i - ctx.n_p)
                            }
                        } else {
                            NestFieldKind::InProgress
                        };
                        Ok((k, w.dup2(), ns))
                    } else {
                        fail(nest_non_valid())
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1498-1507 nestHoles
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestHoles` — the
/// member holes: member `m` is the free variable `nP + m`, typed by its
/// former's type instantiated at the canonical parameters; `none` when a
/// member is not a stored former or its type does not bind the parameters
/// (the cited `mapM`, as an index recursion).
pub fn nest_holes(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    ctx: &NestCtx,
    mm: usize,
    out: Vec<EIdx>,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    if mm >= ctx.names.len() {
        Ok(Some(out))
    } else {
        match ind_cv_of(ctx.vis, fe, &ctx.names[mm]) {
            None => Ok(None),
            Some(cv) => match inst_pis_with(pers, st, &ctx.params, 0, &cv.ty) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(t)) => match intern_e_fvar(pers, st, ctx.n_p + (mm as u64), t) {
                    Err(e) => Err(e),
                    Ok(v) => {
                        let mut o: Vec<EIdx> = out;
                        o.push(v);
                        nest_holes(pers, st, fe, ctx, mm + 1, o)
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1509-1515 nestRootCanon
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestRootCanon` — **the
/// root frame's canonical crest** of a member constructor: its whole member
/// applications abstracted, at the block's levels.
pub fn nest_root_canon(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    cv: &IConstantVal,
) -> Result<Option<EIdx>, CheckError> {
    match expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv.level_params, &ctx.lvls, &cv.ty) {
        Err(e) => Err(e),
        Ok(t) => nest_canon_crest(pers, st, &ctx.names, &ctx.lvls, ctx.n_p, &t),
    }
}

// ---------------------------------------------------------------------------
// Uniform occurrences: official's `check_uniform_ind_occs`
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1543-1548 Expr.piDomsOcc
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean piDomsOcc` — does a
/// member or a hole occur in one of the first `n` binder domains of `e`?
pub fn pi_doms_occ(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lo: u64,
    hi: u64,
    n: u64,
    e: &EIdx,
) -> Result<bool, CheckError> {
    if n == 0 {
        Ok(false)
    } else if e.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, e) {
            None => fail_dangling_e(),
            Some((d, b, _)) => match nest_occ(pers, st, names, lo, hi, &d) {
                Err(er) => Err(er),
                Ok(true) => Ok(true),
                Ok(false) => pi_doms_occ(pers, st, names, lo, hi, n - 1, &b),
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1550-1559 nestUniformOk
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestUniformOk` —
/// **official's `check_uniform_ind_occs` at one constructor**: the parameters'
/// domains name no member, and its canonical crest has no member constant
/// left.
pub fn nest_uniform_ok(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match pi_doms_occ(pers, st, &ctx.names, ctx.n_p, hi_at(ctx, 0), ctx.n_p, &cv.ty) {
        Err(e) => Err(e),
        Ok(true) => Ok(false),
        Ok(false) => match nest_root_canon(pers, st, ctx, cv) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(crest)) => match nest_occ(pers, st, &ctx.names, 0, 0, &crest) {
                Err(e) => Err(e),
                Ok(occ) => {
                    if occ {
                        Ok(false)
                    } else {
                        Ok(true)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1561-1569 nestUniform
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestUniform` — one
/// member's constructors from `i` on: `true` when all pass.
pub fn nest_uniform_member(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= cs.len() {
        Ok(true)
    } else {
        let cv: IConstantVal = env::i_constant_val_dup(&cs[i].0);
        match nest_uniform_ok(pers, st, ctx, &cv) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => nest_uniform_member(pers, st, ctx, cs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1561-1569 nestUniform
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestUniform` —
/// `nestUniformOk` at every stored constructor of every member, before the
/// walk, in order, stopping at the first failure: a REJECT with official's
/// wording (the constructor's name dropped, §3.1).
pub fn nest_uniform(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    ctorss: &Vec<Vec<(IConstantVal, u64)>>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= ctorss.len() {
        Ok(())
    } else {
        match nest_uniform_member(pers, st, ctx, &ctorss[i], 0) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_UNIFORM))),
            Ok(true) => nest_uniform(pers, st, ctx, ctorss, i + 1),
        }
    }
}

// ---------------------------------------------------------------------------
// The root frame and the seeds
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1585-1600 nestRoot
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestRoot` — **the
/// root frame**: every member's constructors through `nestCtors` at the root
/// key (the block's levels, the canonical parameters, the holes above them),
/// member by member, sharing the walk's state; each constructor at the
/// input-derived fuel of its instantiated type.
#[allow(clippy::too_many_arguments)]
pub fn nest_root(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    holes: &Vec<EIdx>,
    ctorss: &Vec<Vec<(IConstantVal, u64)>>,
    i: usize,
    ns: NestState,
    outs: Vec<Vec<(Vec<NestFieldKind>, EIdx)>>,
) -> Result<(Vec<Vec<(Vec<NestFieldKind>, EIdx)>>, NestState), CheckError> {
    if i >= ctorss.len() {
        Ok((outs, ns))
    } else {
        let prog: Vec<NestHole> = Vec::new();
        match nest_ctors(
            pers,
            st,
            mode,
            fe,
            ctx,
            true,
            0,
            &prog,
            hi_at(ctx, 0),
            &ctx.lvls,
            &ctx.params,
            &ctx.names,
            holes,
            &ctorss[i],
            0,
            ns,
            Vec::new(),
        ) {
            Err(e) => Err(e),
            Ok((o, ns2)) => {
                let mut outs2: Vec<Vec<(Vec<NestFieldKind>, EIdx)>> = outs;
                outs2.push(o);
                nest_root(pers, st, mode, fe, ctx, holes, ctorss, i + 1, ns2, outs2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1630-1638 nestSeedOf
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestSeedOf` — one
/// parameter of a resolved class moved to the walk's representation: its
/// whole member applications abstracted to the canonical holes, then every
/// free variable replaced whole by the canonical parameter or the hole.
pub fn nest_seed_param(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    holes: &Vec<EIdx>,
    x: &EIdx,
) -> Result<EIdx, CheckError> {
    match replace_apps(pers, st, &ctx.names, &ctx.lvls, 0, ctx.n_p, x) {
        Err(e) => Err(e),
        Ok(y) => {
            let f: FvMap = FvMap::KeyMap(env::eidx_vec_dup(&ctx.params), env::eidx_vec_dup(holes));
            replace_fvars(pers, st, &f, &y)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1630-1638 nestSeedOf
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestSeedOf` — the
/// class's parameters, each moved (`ds.map …`, in order).
pub fn nest_seed_params(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    holes: &Vec<EIdx>,
    ds: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= ds.len() {
        Ok(out)
    } else {
        let x: EIdx = ds[i].dup2();
        match nest_seed_param(pers, st, ctx, holes, &x) {
            Err(e) => Err(e),
            Ok(y) => {
                let mut o: Vec<EIdx> = out;
                o.push(y);
                nest_seed_params(pers, st, ctx, holes, ds, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1630-1638 nestSeedOf
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestSeedOf` — **a
/// resolved class as a seed**: the outside class `I.{us} ds` in the walk's
/// representation, with its parameter count.
#[allow(clippy::too_many_arguments)]
pub fn nest_seed_of(
    pers: &PersTier,
    st: &mut AState,
    ctx: &NestCtx,
    holes: &Vec<EIdx>,
    i_name: &NIdx,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    n_pc: u64,
) -> Result<(NestKey, u64), CheckError> {
    match nest_seed_params(pers, st, ctx, holes, ds, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(ds2) => Ok((
            NestKey {
                cname: i_name.dup2(),
                lvls: us.dup2(),
                ds: ds2,
            },
            n_pc,
        )),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1640-1654 nestSeeds
/// Lean twin: `key.ds.foldl (fun a d => max a (whnfWalkFuel d)) fuelSlack` — a
/// seed's fuel, left to right.
pub fn seed_fuel(pers: &PersTier, st: &AState, ds: &Vec<EIdx>, i: usize, acc: u64) -> Result<u64, CheckError> {
    if i >= ds.len() {
        Ok(acc)
    } else {
        match whnf_walk_fuel(pers, st, &ds[i]) {
            Err(e) => Err(e),
            Ok(f) => seed_fuel(pers, st, ds, i + 1, max_u64(acc, f)),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1640-1654 nestSeeds
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean nestSeeds` — **the
/// seeds walked**, in order, at the root: each class a container instance met
/// at the empty frame stack (`nestContKey`), at the fuel its parameters'
/// depths give.
#[allow(clippy::too_many_arguments)]
pub fn nest_seeds(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    seeds: &Vec<(NestKey, u64)>,
    i: usize,
    ns: NestState,
) -> Result<NestState, CheckError> {
    if i >= seeds.len() {
        Ok(ns)
    } else {
        let key: NestKey = nest_key_dup(&seeds[i].0);
        let n_pc: u64 = seeds[i].1;
        match seed_fuel(pers, st, &key.ds, 0, FUEL_SLACK) {
            Err(e) => Err(e),
            Ok(f) => match nest_inst_type(pers, st, fe, ctx, hi_at(ctx, 0), &key) {
                Err(e) => Err(e),
                Ok((_, cty)) => {
                    let prog: Vec<NestHole> = Vec::new();
                    match nest_cont_key(
                        pers, st, mode, fe, ctx, f, &prog, 0, &key.cname, &key.lvls, &key.ds, n_pc, &cty, ns,
                    ) {
                        Err(e) => Err(e),
                        Ok((_, ns2)) => nest_seeds(pers, st, mode, fe, ctx, seeds, i + 1, ns2),
                    }
                }
            },
        }
    }
}
