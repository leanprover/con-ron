//! **The pure checker core's syntactic layer** —
//! `ConLeche/Kernel/Core.lean`'s readers, pinned tables, install-time rule
//! bits and small helpers, plus the three fuel constants of the knot's loops
//! and `checkFuel` (`:2903`).  The head of the file (`CheckError`, `CheckM`)
//! is `core_types.rs` (task #14).
//!
//! The module is `core_k`, not `core`: `core` is a Rust prelude crate name,
//! and `crate::kernel::core` would shadow it for every `use` inside this
//! crate.  The `k` is for *kernel* — con-leche's `ConLeche.Kernel.Core`.
//!
//! ## What is here and what moved (task #23)
//!
//! Task #18 ported `Kernel/Core.lean`'s *bodies* here and tied them with
//! `Cached/CoreC.lean`'s wrappers.  `CoreC.lean` has its own twin of almost
//! every one of those bodies, and it is the twins the executed checker runs:
//! they read the level operations through `lsimpC`/`lnzC`/`eqvC`, the stored
//! constants through `ienv`/`constTyAt`/`constValAt`/`ruleRhsAt`, and the
//! bulk instantiations through `instC`, and five of them are a different
//! *algorithm* (bulk beta, the head-normalization loop, bulk telescope
//! consumption, the binder-telescope loops).  Task #23 ported them and
//! re-pointed the knot, so **the bodies are now
//! `crate::cached::core_c`** and the ones here are gone: a superseded body
//! threads the same knot, so keeping it would have doubled the mutual block
//! of the generated Lean for functions nothing executes (DESIGN.md §3.1).
//! Their `Core.lean` citations are the second `con-leche:` line on the twin
//! in `core_c`.
//!
//! What stays here is everything the cached bodies *call*:
//!
//! * the syntactic readers and guards — `unfoldable_head`, `head_hint`,
//!   `same_const_heads`, `raw_nat_lit`, `is_ctor_app`,
//!   `eta_ctor_shape`, `is_bool_true`, `succ_of`,
//!   `str_expansion_fires`, `pw_written`, `lift_fueled`.  **Six of these
//!   carry a second citation to `Cached/StateC.lean`'s `*C` index guards**
//!   (`isCtorAppC`, `headHintC`, `unfoldableHeadC`,
//!   `sameConstHeadsC`, `rawNatLitC?`, `etaCtorShapeC`): those are the same
//!   function, since the port reads the environment through `FEnv` anyway
//!   (deviation 3 below).  So are `litToCtorIfNatI` and `annotBinderMetaI`,
//!   whose twins are the spec's under a `pure`;
//! * the pinned name tables and the `Nat`-operation pin sets;
//! * the install-time rule bits (`rec_rule_bits`,
//!   `rec_rule_k`) and the shape conjunctions the cached certificates read
//!   (`struct_eta_shape_ok`, `unit_shape_ok`, `proj_fire_shape_ok`,
//!   `fab_scope_ok`, `proj_entry_fire_ok`, `and_rescue_slots`);
//! * the pure pieces of the inference clauses (`infer_fvar`,
//!   `infer_lit_nat`, `infer_lit_str`, `infer_proj_at`,
//!   `proj_type_at_checked`, `proj_entry_type_at`);
//! * the four loop budgets (`whnf_core_loop_fuel`, `whnf_loop_fuel`,
//!   `defeq_loop_fuel`, `check_fuel`);
//! * the `Vec` helpers and the owning environment probes.
//!
//! Four functions here are **dead and deliberately kept**, as task #18's
//! eleven were, so the provenance ledger stays in step with its source:
//! `beta_gate_fires` (the pure β gate; the cached sites read
//! `mode.betaSkip`), `eta_projs`/`eta_projs_from` (superseded by
//! `core_c::proj_apps_i`, but `eta_fab_args_e` is written
//! against them, and all three are dead in the Lean too), and `consts_resolve` (whose
//! memoized `ExprC` twin is `state_c::consts_resolve_fc`).
//!
//! ## The knot is closed by name, not by a record (DESIGN.md §3.1)
//!
//! `Kernel/Core.lean`'s bodies are non-recursive, written against a record
//! `r : CoreFns m` of the six mutually recursive entry points.  The port
//! drops the record: where a body writes `r.whnf d x` the Rust writes
//! `core_c::whnf(mode, fuel, st, fe, d, &x)` — the *wrapper*, by name — and
//! the record's parameter is replaced by the `fuel: u64` the wrapper
//! decrements.  The whole set (the bodies in `core_c` and its six wrappers)
//! is one block of plain mutually recursive functions; no trait is in the
//! recursion and there are no closures.
//!
//! Four consequences, each a deviation from the cited text that applies
//! *everywhere* and is therefore recorded once rather than on every item:
//!
//! 1. **`mode` is threaded explicitly.**  In the Lean the knot closes over
//!    the mode, so a body that reads no mode itself takes none.
//! 2. **The state is `&mut CState`** — `CheckCM`'s `StateT CState`.  No
//!    function *in this module* takes it any more; that is the measure of
//!    what moved.
//! 3. **The environment is the index `FEnv`.**  `Kernel/Core.lean`'s bodies
//!    take `env : Env` and call `env.find?`/`env.findProj?`; the executed
//!    checker reads through the index, and con-leche writes the `F`-mirror
//!    twins (`FEnv.lean:98-153`) and the `*C` guards (`StateC.lean:48-112`)
//!    for exactly that.  The port has one spelling, `fe: &FEnv` with
//!    `fenv::find`/`fenv::find_proj`, so those twins are *one* Rust function
//!    with two or three citations.
//! 4. **Depths, indices and arities are `u64`** (DESIGN.md §3.3); only
//!    `Literal.natVal` and the `Nat`-operation fast path use `ron::Nat`.
//!
//! ## The other standing deviations
//!
//! * **`List` becomes `Vec` with `*_from` index helpers** (task #3's
//!   pattern): `pi_residual`, `nat_op_deps`, `and_rescue_slots` and friends.
//!   `List.take`/`.drop`/`++` copy a `Vec` spine (`take_exprs`,
//!   `drop_exprs`, `append_exprs`) where Lean's sharing is free.
//! * **`&&`/`∧` cascades become `if` nests** (task #3's pattern 9), so the
//!   generated Lean keeps the cited short-circuit order.
//! * **Lean string literals are `const […]: [u32; N]` code points**
//!   (DESIGN.md §3.3, task #14): every throw site carries its message as a
//!   `const` in its own body and builds it with `core_types::code_points`.
//!   Interpolated messages (`s!"unknown constant {n}"`) drop the
//!   interpolation — DESIGN.md §3.1: message strings need not match, the
//!   theorem never reads them.
//! * **A pattern's fields are copied into owned locals** (`expr::dup`, an
//!   `P` bump) wherever they outlive the `match`; this is what Lean's value
//!   semantics gives for free, and it is task #14's rule against holding a
//!   borrow across a state-touching branch.

use crate::kernel::basis_names;
use crate::kernel::core_types;
use crate::kernel::name;
use crate::kernel::name::Name;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// `Vec` helpers for the `List` operations the Lean uses for free
// ---------------------------------------------------------------------------

/// con-leche: none — Lean's `toString` on a `Nat` (the runtime's `Nat.repr`)
/// `toString i` for a `Nat` index: the decimal code points, most significant
/// digit first, `0` for zero.  Lean's `Nat.toString` is the runtime's; on the
/// `u64` of DESIGN.md §3.3 this is the recursion that produces it.
pub fn nat_to_dec(i: u64) -> Vec<u32> {
    nat_to_dec_go(i, Vec::new())
}

/// con-leche: none — Lean's `toString` on a `Nat` (the runtime's `Nat.repr`)
/// The digit recursion behind `nat_to_dec`: the quotient's digits are pushed
/// before the last one, so the result is most-significant first.
pub fn nat_to_dec_go(i: u64, out: Vec<u32>) -> Vec<u32> {
    if i < 10 {
        let mut out = out;
        out.push(48 + (i as u32));
        out
    } else {
        let mut out = nat_to_dec_go(i / 10, out);
        out.push(48 + ((i % 10) as u32));
        out
    }
}

// ---------------------------------------------------------------------------
// The certified structural-`Nat` operations (`Core.lean:505-775`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:359 natPredName
/// `Nat.pred`.
pub fn nat_pred_name() -> Name {
    const S: [u32; 4] = [112, 114, 101, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:360 natAddName
/// `Nat.add`.
pub fn nat_add_name() -> Name {
    const S: [u32; 3] = [97, 100, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:361 natSubName
/// `Nat.sub`.
pub fn nat_sub_name() -> Name {
    const S: [u32; 3] = [115, 117, 98];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:362 natMulName
/// `Nat.mul`.
pub fn nat_mul_name() -> Name {
    const S: [u32; 3] = [109, 117, 108];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:363 natPowName
/// `Nat.pow`.
pub fn nat_pow_name() -> Name {
    const S: [u32; 3] = [112, 111, 119];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:364 natBeqName
/// `Nat.beq`.
pub fn nat_beq_name() -> Name {
    const S: [u32; 3] = [98, 101, 113];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:365 natBleName
/// `Nat.ble`.
pub fn nat_ble_name() -> Name {
    const S: [u32; 3] = [98, 108, 101];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:366 natDivName
/// `Nat.div`.
pub fn nat_div_name() -> Name {
    const S: [u32; 3] = [100, 105, 118];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:367 natModName
/// `Nat.mod`.
pub fn nat_mod_name() -> Name {
    const S: [u32; 3] = [109, 111, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:368 natGcdName
/// `Nat.gcd`.
pub fn nat_gcd_name() -> Name {
    const S: [u32; 3] = [103, 99, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:369 natLandName
/// `Nat.land`.
pub fn nat_land_name() -> Name {
    const S: [u32; 4] = [108, 97, 110, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:370 natLorName
/// `Nat.lor`.
pub fn nat_lor_name() -> Name {
    const S: [u32; 3] = [108, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:371 natXorName
/// `Nat.xor`.
pub fn nat_xor_name() -> Name {
    const S: [u32; 3] = [120, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:372 natShiftLeftName
/// `Nat.shiftLeft`.
pub fn nat_shift_left_name() -> Name {
    const S: [u32; 9] = [115, 104, 105, 102, 116, 76, 101, 102, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:373 natShiftRightName
/// `Nat.shiftRight`.
pub fn nat_shift_right_name() -> Name {
    const S: [u32; 10] = [115, 104, 105, 102, 116, 82, 105, 103, 104, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:374 boolName
/// `Bool`.
pub fn bool_name() -> Name {
    const S: [u32; 4] = [66, 111, 111, 108];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:375 boolTrueName
/// `Bool.true`.
pub fn bool_true_name() -> Name {
    const S: [u32; 4] = [116, 114, 117, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:376 boolFalseName
/// `Bool.false`.
pub fn bool_false_name() -> Name {
    const S: [u32; 5] = [102, 97, 108, 115, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}

// ---------------------------------------------------------------------------
// The annotation pass (`Core.lean:2677-2858`)
// ---------------------------------------------------------------------------

/* Not ported from `Kernel/Core.lean` (DESIGN.md §3.1), and why:

   * `instance : ToString CheckError` (`:53-57`) — rendering only; §3.1 says
     message strings need not match, and the CLI (outside the verified core)
     renders errors.  Already recorded by task #14, which ported the
     `CheckError` half of the file.
   * the eight `@[simp] theorem`s about `recRuleBits` (`:1545-1586`) and the
     four about `projFnRule` (`:1596-1613`) — field-projection equations,
     i.e. the *spec* this port will be proved against, not part of it.

   Everything else in the file is either here or in `crate::cached::core_c`,
   whose twin of it is what the knot executes (the module note's "What is
   here and what moved").  `structure CoreFns` (`:66-92`) and
   `CoreFns.ioView` (`:89-95`) are cited on `core_c::infer_at_i`, the `io`
   flag that *is* the record's slot dispatch; `coreKnot` (`:2866-2900`) is
   cited on `core_c`'s six wrappers, which are `coreKnotI`'s.

   The `FEnv.lean` guards that read the same bodies through the index
   (`natLitSupportedF`, `strLitSupportedF`, `natOpGuardF`, `natOpStoredF`,
   `andRescueSlotsF`, `towerSlotsAllF`, `recSlotsAllF`) and the seven
   `StateC.lean` `*C` index guards are covered by the corresponding function
   here, with a second citation, per the module note's deviation 3. */
#[cfg(test)]
mod tests {
    // Task #97-SWAP: this module's tests ran the `Expr`-tree checker
    // (`cached::core_c`, `cached::state_c`) over the items above, and that
    // checker is gone — the arena's is the checker now.  What the items are
    // still FOR is the pinned DATA (`lib.rs`'s "Why `Expr` survives"), which
    // `arena::intern` reads and `crates/con-ron-core/src/arena/*`'s own tests
    // and `scripts/diff-e2e.sh` exercise end to end.
}
