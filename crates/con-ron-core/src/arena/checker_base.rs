//! `arena::checker_base` — the declaration checker's common ground.
//!
//! The Rust twin of `proof/ConRon/Arena/CheckerBase.lean`, which is
//! con-leche's `Kernel/CheckerBase.lean`: the core entry-point record, the
//! common per-declaration constant check, and the strategy-independent helpers
//! the install paths share.
//!
//! ## The four systematic deviations, and the two the port adds
//!
//! 1. **`env : Env` is `fe : IFEnv`** — `arena::core`'s deviation 1.  con-leche
//!    carries each of these functions twice, once reading the linear
//!    association list and once the index (`DeclCheck.lean`'s `…F` mirrors);
//!    the arena has ONE environment type, so each pair collapses into one twin
//!    carrying a `con-leche:` line per collapsed declaration.
//! 2. **`CheckerOps` is not a record here at all.**  DESIGN.md §8.2 is explicit
//!    that it is "a program seam at HEAD, not a proof seam"; §3.4 forbids a
//!    record of function values, and `con_ron_core::kernel::checker_base` drops
//!    the `ops` binder for exactly that reason.  The Lean twin keeps
//!    `CheckerOpsA`/`fueledOpsA`/`pureOpsA` as the statement subjects P3 will
//!    need — the treatment task #97c gives `CoreIO.lean`/`CoreGated.lean` — and
//!    they have **no Rust counterpart**, exactly as `pureFnsA` has none
//!    (`arena::core`'s `PURE_FNS_A` is the lane constant that replaces it).
//!    Every body below calls `arena::core`'s fueled entry points by name.
//! 3. **`orElse` is `or_else_attempt`, the four-way step**, and it is the one
//!    place in (C) that recovers from a thrown error.  See its own note.
//! 4. **A `g : Nat → Expr → Expr` argument is not a function value.**
//!    `domsMatchAux` is called at the identity everywhere in this module, so
//!    the twin here is the identity one and it is PURE: over handles a domain
//!    comparison is a handle comparison.
//!
//! The port's own two:
//!
//! 5. **`mentionsConst` is here, not in `arena::inductives`.**  The Lean twin
//!    puts it in `Arena/Inductives/StructParts.lean`, which sits *below*
//!    `CheckerBase.lean` in the Lean import order; the Rust module graph has
//!    `arena::inductives` *above* this module (it calls `check_ind_decl`), so
//!    the walk is spelled here, at its one caller.  Task #97d's own "IndBase
//!    duplication" note is the Lean-side record of the same seam.
//! 6. **`or_else_attempt`'s state restore is the WHOLE state** (tasks
//!    #97-T2-LOCKSTEP D4b, D4c).  The twin writes the attempt as a state
//!    function, which makes the whole pre-attempt state free; `&mut AState`
//!    has no such thing.  The caller moves the persistent tier aside
//!    (`arena::checker::freeze_tier`, O(1)), copies the rest of the state
//!    (`attempt_snapshot`: scratch tiers, memos, caches, pins, flags — the
//!    persistent tables are empty by then), runs the attempt against the
//!    frozen tier, and on `Recovered` moves the copy back and thaws the tier
//!    into it.  History: task #97-P4d's `astate_dup` copied the whole store
//!    with a recursion one frame per node and overflowed the stack on
//!    `Init`+`Std`+`Lean`'s `Nat.mod` (12.3 M nodes); task #97-P6-2 then
//!    restored only the caches, D4 added the scratch tiers (a kept scratch
//!    node shifts every later scratch handle's word), which is the whole state
//!    only given a frame over the attempt's 1 187-function closure; D4b copied
//!    everything (+6.4 % instructions on `Init`); D4c moves the persistent
//!    tier instead of copying it, which is exact by construction because the
//!    attempt reads it through the frozen `PersTier` and cannot write it.

use crate::arena::core::{
    annotate_core, append_eidx, consts_resolve, ensure_sort_core, infer_type_core, is_def_eq_core,
    reserved_basis_names, zero_level, CHECK_FUEL, CORE_WALK_FUEL, M_SORRY, M_UNKNOWN_CONST,
};
use crate::arena::core_state::Caches;
use crate::arena::env::{
    i_constant_info_dup, i_constant_info_to_constant_val, ifenv_find, nidx_vec_dup, IConstantInfo,
    IConstantVal, IFEnv,
};
use crate::arena::expr_ops::{
    cons_eidx, fvar_type_d, get_app_args, get_app_fn, has_fvar_fast, inst_lams_at_f, inst_pis_at_f,
    instantiate1_fast, instantiate_list_fast, loose_bvars_bounded_fast, pi_result, pis_to_lams,
    strip_lams, strip_pis,
};
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_CONST, ETAG_FORALL_E, ETAG_SORT, NTAG_STR, NTAG_NUM};
use crate::arena::monad::{
    AState, Memos, fail, fail_dangling_e, intern_e_bvar, intern_e_fvar, read_level, read_levels, read_names, view, view_bind, view_const, view_const_name, view_ls, view_n, view_sort,
};
use crate::arena::store::{ENodeView, NNodeView};
use crate::arena::pins::{pin_eq, pin_sorry_ax, Pins};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::expr::BinderMeta;
use crate::kernel::expr_ops::sub_nat;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines (con-ron-core's own spellings, so
// that a differential test can compare error text; §3.1 — a message need not
// match a theorem — and the twin's interpolated names are dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"duplicate declaration"`, as code points.
pub const M_DUP_DECL: [u32; 21] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
    110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"reserved basis name"`, as code points.
pub const M_RESERVED_BASIS: [u32; 19] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"reserved projection name"`, as code points.
pub const M_RESERVED_PROJ: [u32; 24] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110,
    32, 110, 97, 109, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"duplicate universe parameters in declaration"`, as code points.
pub const M_DUP_UNIV: [u32; 44] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112,
    97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97,
    116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"loose bound variable in type"`, as code points.
pub const M_LOOSE_TYPE: [u32; 28] = [
    108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101,
    32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unexpected free variable in type"`, as code points.
pub const M_FVAR_TYPE: [u32; 32] = [
    117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105,
    97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"undeclared universe parameter in type"`, as code points.
pub const M_UNDECL_TYPE: [u32; 37] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
    112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: allLevelParamsDefined"`, as code points.
pub const M_FUEL_ALPD: [u32; 37] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 108, 108, 76,
    101, 118, 101, 108, 80, 97, 114, 97, 109, 115, 68, 101, 102, 105, 110, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: constsResolveF"`, as code points.
pub const M_FUEL_CRF: [u32; 30] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 99, 111, 110, 115,
    116, 115, 82, 101, 115, 111, 108, 118, 101, 70,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: mentionsConst"`, as code points.
pub const M_FUEL_MENTIONS: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 109, 101, 110, 116,
    105, 111, 110, 115, 67, 111, 110, 115, 116,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"nested pin type mismatch"`, as code points.
pub const M_NESTED_PIN_TYPE: [u32; 24] = [
    110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 116, 121, 112, 101, 32, 109, 105, 115,
    109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"nested pin arity mismatch"`, as code points.
pub const M_NESTED_PIN_ARITY: [u32; 25] = [
    110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 114, 105, 116, 121, 32, 109, 105, 115,
    109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"nested pin annotation mismatch"`, as code points.
pub const M_NESTED_PIN_ANNOT: [u32; 30] = [
    110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111,
    110, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"iota statement component mismatch"`, as code points.
pub const M_IOTA_COMP_MISMATCH: [u32; 33] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109, 112, 111,
    110, 101, 110, 116, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"iota statement component arity"`, as code points.
pub const M_IOTA_COMP_ARITY: [u32; 30] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109, 112, 111,
    110, 101, 110, 116, 32, 97, 114, 105, 116, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection type telescope"`, as code points.
pub const M_PROJ_TYPE_TELE: [u32; 25] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116, 101, 108,
    101, 115, 99, 111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection constructor telescope"`, as code points.
pub const M_PROJ_CTOR_TELE: [u32; 32] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection constructor residual arity"`, as code points.
pub const M_PROJ_CTOR_ARITY: [u32; 37] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 114, 101, 115, 105, 100, 117, 97, 108, 32, 97, 114, 105, 116, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection constructor residual head"`, as code points.
pub const M_PROJ_CTOR_HEAD: [u32; 36] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 114, 101, 115, 105, 100, 117, 97, 108, 32, 104, 101, 97, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection rule telescope"`, as code points.
pub const M_PROJ_RULE_TELE: [u32; 25] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 116, 101, 108,
    101, 115, 99, 111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection rule scoping"`, as code points.
pub const M_PROJ_RULE_SCOPING: [u32; 23] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 115, 99, 111, 112,
    105, 110, 103,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection rule wellformedness"`, as code points.
pub const M_PROJ_RULE_WF: [u32; 30] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 119, 101, 108,
    108, 102, 111, 114, 109, 101, 100, 110, 101, 115, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection rule body"`, as code points.
pub const M_PROJ_RULE_BODY: [u32; 20] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 98, 111, 100, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection rule domain mismatch"`, as code points.
pub const M_PROJ_RULE_DOMAIN: [u32; 31] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 100, 111, 109, 97,
    105, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

// ---------------------------------------------------------------------------
// The state snapshot (`CheckerBase.lean:113-139`'s `orElseAttempt`, deviation 6)
// ---------------------------------------------------------------------------

/// con-leche: none — a `Vec` copy; Lean's value semantics hides it (DESIGN.md §3.2)
/// Every `Vec` copy of the snapshot below: the journals of `Caches`.
pub fn vec_dup<T: Dup>(xs: &Vec<T>) -> Vec<T> {
    let n = xs.len();
    vec_dup_range(xs, Vec::with_capacity(n), 0, n)
}

/// con-leche: none — a `Vec` copy; Lean's value semantics hides it (DESIGN.md §3.2)
/// `vec_dup`'s walk over `[lo, hi)`, pushing the copies onto `out` in index
/// order.  **Halved rather than peeled one at a time**, so the recursion is
/// `log2 n` deep — `con_ron_core::ron::hashmap::HashMap::dup_slots`' own
/// shape, and for its own reason: a peeling recursion is one frame per
/// element, which is a stack overflow on a long `Vec` (task #97-P6-2 found it
/// as one, at `Init`+`Std`+`Lean`'s `Nat.mod`).  The left half is copied
/// first, which is what keeps the pushes in order; the accumulator is passed
/// by value and returned (task #6's rule).
pub fn vec_dup_range<T: Dup>(xs: &Vec<T>, out: Vec<T>, lo: usize, hi: usize) -> Vec<T> {
    if hi > lo {
        let n = hi - lo;
        if n == 1 {
            let mut out2 = out;
            out2.push(xs[lo].dup2());
            out2
        } else {
            let mid = lo + n / 2;
            let out2 = vec_dup_range(xs, out, lo, mid);
            vec_dup_range(xs, out2, mid, hi)
        }
    } else {
        out
    }
}

/// con-leche: none — the per-call memo tables, copied
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:134-163 orElseAttempt`.
pub fn memos_dup(m: &Memos) -> Memos {
    Memos {
        inst1_c: m.inst1_c.dup(),
        inst_l_c: m.inst_l_c.dup(),
        lift_c: m.lift_c.dup(),
        reset_c: m.reset_c.dup(),
        rename_c: m.rename_c.dup(),
        abs1_c: m.abs1_c.dup(),
        lower_c: m.lower_c.dup(),
        inst1_l_c: m.inst1_l_c.dup(),
        inst_lp_c: m.inst_lp_c.dup(),
        bvar_b_c: m.bvar_b_c.dup(),
        fvar_b_c: m.fvar_b_c.dup(),
        inst_lp_l_c: m.inst_lp_l_c.dup(),
        inst_lp_ls_c: m.inst_lp_ls_c.dup(),
    }
}

/// con-leche: none — the per-declaration caches, copied
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:134-163 orElseAttempt`.
pub fn caches_dup(c: &Caches) -> Caches {
    Caches {
        whnf_core_c: c.whnf_core_c.dup(),
        whnf_c: c.whnf_c.dup(),
        infer_c: c.infer_c.dup(),
        infer_io_c: c.infer_io_c.dup(),
        annot_c: c.annot_c.dup(),
        defeq_c: c.defeq_c.dup(),
        lvl_eq_c: c.lvl_eq_c.dup(),
        lvls_eq_c: c.lvls_eq_c.dup(),
        const_ty_c: c.const_ty_c.dup(),
        const_val_c: c.const_val_c.dup(),
        rule_rhs_c: c.rule_rhs_c.dup(),
        // The readback memo (task #97-P6-13) is copied too (task
        // #97-T2-LOCKSTEP D4).  It used to be restored EMPTY, on the argument
        // that `denoteL`/`denoteN`/`denoteLs` are functions of the store so an
        // empty memo loses rows and nothing else — true of the answers, false
        // of the state: the twin resumes a recovered attempt with its
        // pre-attempt `readLC`/`readNC`/`readLsC`, and the lockstep relation
        // compares the tables key by key.  Eight snapshots on the whole of
        // `Init` (task #97-P6-4a §4) make the three copies free.
        read_l_c: c.read_l_c.dup(),
        read_n_c: c.read_n_c.dup(),
        read_ls_c: c.read_ls_c.dup(),
    }
}

/// con-leche: none — the reserved-name pins, copied
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:134-163 orElseAttempt`.
pub fn pins_dup(p: &Pins) -> Pins {
    Pins {
        names: vec_dup(&p.names),
        reserved: vec_dup(&p.reserved),
        empty_levels: p.empty_levels.dup2(),
        zero_level: p.zero_level.dup2(),
        sort_one: p.sort_one.dup2(),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:134-163 orElseAttempt` —
/// take the snapshot, before the attempt runs: **a full copy of the whole
/// checker state** (task #97-T2-LOCKSTEP D4b) — the four stores with both
/// tiers, their cons tables and their flags (`EStore::dup`), the memos, the
/// caches and the pins.  Its one caller
/// (`arena::decl_check::check_div_mod_pin_attempt`) takes it AFTER moving the
/// persistent tier aside (task #97-T2-LOCKSTEP D4c), so the persistent tables
/// it copies are empty and the copy is `O(scratch + caches)`.  Every copy is
/// a halved recursion (`Tbl::dup`, `HashMap2::dup`, `vec_dup`), so it is
/// `log2 n` deep.
pub fn attempt_snapshot(st: &AState) -> AState {
    AState {
        store: st.store.dup(),
        memos: memos_dup(&st.memos),
        caches: caches_dup(&st.caches),
        pins: pins_dup(&st.pins),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:134-163 orElseAttempt` —
/// the restore of `OrElseStep::Recovered`: the snapshot is MOVED back as the
/// whole state, so everything the attempt did goes (module note 6).
pub fn attempt_restore(st: &mut AState, snap: AState) {
    *st = snap;
}

// ---------------------------------------------------------------------------
// The variant fallback (`CheckerBase.lean:87-139`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:93-111 OrElseStep` — what
/// `orElse` decides once the attempt has run.  con-leche's clause is
/// three-way; the port's is four, and the arena's is the port's:
///
/// ```text
/// | .ok (true,  s') => .ok ((), s')     ->  Matched
/// | .ok (false, s') => k none      s'   ->  Continued   (post-attempt state)
/// | .error e        => k (some e)  s    ->  Recovered e (PRE-attempt state)
///                                       ->  Failed e    when e is `native`
/// ```
///
/// `Failed` carries **only** a `Native` error (DESIGN.md §8.3's ruling, task
/// #67's for the Rust port): the arena's own machine-word limit has no `throw`
/// behind it in con-leche, so "con-leche would have recovered from this too"
/// is a claim about a run the cited checker never has.  The stream declines
/// instead; an accept-direction deviation that can only lose acceptances.
pub enum OrElseStep {
    Matched,
    Continued,
    Recovered(CheckError),
    Failed(CheckError),
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:134-163 orElseAttempt` —
/// **the attempt's verdict.**  This is the ONE place (C) recovers from a
/// thrown error, and it is scoped to one `Nat.div`/`Nat.mod` pin variant's
/// attempt: a certificate blob generated by another toolchain can be ill-typed
/// against this stream, and that is "this variant does not match", not a
/// checker bug.
///
/// The twin is a state function, so restoring the pre-attempt state is free
/// there; here the decision is pure and the caller
/// (`arena::decl_check::check_div_mod_pin_attempt`) restores its own
/// `attempt_snapshot` on `Recovered` (`attempt_restore`), the twin's
/// `orElseAttempt` restoring its snapshot.
pub fn or_else_attempt(attempt: Result<bool, CheckError>) -> OrElseStep {
    match attempt {
        Ok(true) => OrElseStep::Matched,
        Ok(false) => OrElseStep::Continued,
        Err(e) => match e {
            CheckError::Native(m) => OrElseStep::Failed(CheckError::Native(m)),
            _ => OrElseStep::Recovered(e),
        },
    }
}

// ---------------------------------------------------------------------------
// Name-shape tests (`CheckerBase.lean:141-172`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:172-177 nameNodup` — no
/// duplicates in a list of name HANDLES.  A name comparison is a handle
/// comparison (DESIGN.md §8.3: `denoteN` is injective).
pub fn name_nodup(ns: &Vec<NIdx>) -> bool {
    name_nodup_from(ns, 0)
}

/// con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup
/// The cited `List` recursion as an index recursion over the tail `ns[i..]`.
pub fn name_nodup_from(ns: &Vec<NIdx>, i: usize) -> bool {
    if i >= ns.len() {
        true
    } else if nidx_contains_from(ns, i + 1, &ns[i]) {
        false
    } else {
        name_nodup_from(ns, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup
/// The cited `ns.contains n` over the tail.
pub fn nidx_contains_from(ns: &Vec<NIdx>, i: usize, n: &NIdx) -> bool {
    if i >= ns.len() {
        false
    } else if ns[i].eq2(n) {
        true
    } else {
        nidx_contains_from(ns, i + 1, n)
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:218-221 Name.isModelSuffix
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:179-186 NIdx.isModelSuffix`
/// — is this a `_model`-suffixed name (the shape of model companions)?
pub fn nidx_is_model_suffix(pers: &PersTier, st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    const S: [u32; 6] = [95, 109, 111, 100, 101, 108];
    if n.tag() == NTAG_STR {
        match view_n(pers, st, n) {
            Err(e) => Err(e),
            Ok(NNodeView::Str(_, s)) => Ok(name::str_eq(&s, &code_points(&S))),
            Ok(_) => Ok(false),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:223-230 Name.isProjFnShape
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:188-202 NIdx.isProjFnShape`
/// — is this shaped like an installed projection function's name
/// (`(T.proj).i`) or a projection table's (`(T.projTable).0`)?  Both shapes
/// are reserved for the checker's own installs.
pub fn nidx_is_proj_fn_shape(pers: &PersTier, st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    const P: [u32; 4] = [112, 114, 111, 106];
    const T: [u32; 9] = [112, 114, 111, 106, 84, 97, 98, 108, 101];
    if n.tag() == NTAG_NUM {
        match view_n(pers, st, n) {
            Err(e) => Err(e),
            Ok(NNodeView::Num(p, _)) => {
                if p.tag() == NTAG_STR {
                    match view_n(pers, st, &p) {
                        Err(e) => Err(e),
                        Ok(NNodeView::Str(_, s)) => Ok(name::str_eq(&s, &code_points(&P))
                            || name::str_eq(&s, &code_points(&T))),
                        Ok(_) => Ok(false),
                    }
                } else {
                    Ok(false)
                }
            }
            Ok(_) => Ok(false),
        }
    } else {
        Ok(false)
    }
}

// ---------------------------------------------------------------------------
// Level parameters, defined (`CheckerBase.lean:174-232`)
// ---------------------------------------------------------------------------

/// con-leche: none — probe a `EIdx ↦ Bool` walk memo (task #97-P4c's extraction rule 5)
/// A `HashMap::get` match that produces a value is its own function; never
/// inlined.
pub fn memo_b_get(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:218-255
/// allLevelParamsDefinedGo` — the memoized walk.  `params` are transient names
/// (DESIGN.md §8.3's lesson 4: a level algorithm runs on trees, so the
/// parameter list is read back once at the entry); the memo is keyed on the
/// node, which is what makes a shared subterm cost one probe.  It is threaded
/// as a `&mut` where the twin threads it as an argument and a result.
pub fn all_level_params_defined_go(
    pers: &PersTier,
    st: &AState,
    params: &Vec<Name>,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ALPD)))
    } else {
        match memo_b_get(memo, h) {
            Some(r) => Ok(r),
            None => match all_level_params_defined_node(pers, st, params, memo, fuel - 1, h) {
                Err(e) => Err(e),
                Ok(r) => {
                    memo.insert(h.dup2(), r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:218-255
/// allLevelParamsDefinedGo` — the arms, past the probe.
pub fn all_level_params_defined_node(
    pers: &PersTier,
    st: &AState,
    params: &Vec<Name>,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::BVar(_)) => Ok(true),
        Ok(ENodeView::Lit(_)) => Ok(true),
        Ok(ENodeView::Sort(u)) => match read_level(pers, st, &u) {
            Err(e) => Err(e),
            Ok(l) => Ok(level::all_params_defined(params, &l)),
        },
        Ok(ENodeView::Const(_, us)) => match read_levels(pers, st, &us) {
            Err(e) => Err(e),
            Ok(ls) => Ok(all_params_defined_list(params, &ls, 0)),
        },
        Ok(ENodeView::FVar(_, t)) => all_level_params_defined_go(pers, st, params, memo, fuel, &t),
        Ok(ENodeView::App(f, a)) => match all_level_params_defined_go(pers, st, params, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok(b1) => {
                if b1 {
                    all_level_params_defined_go(pers, st, params, memo, fuel, &a)
                } else {
                    Ok(false)
                }
            }
        },
        Ok(ENodeView::Lam(t, b, m)) => {
            all_level_params_defined_binder(pers, st, params, memo, fuel, &t, &b, &m)
        }
        Ok(ENodeView::ForallE(t, b, m)) => {
            all_level_params_defined_binder(pers, st, params, memo, fuel, &t, &b, &m)
        }
        Ok(ENodeView::LetE(t, v, b)) => {
            match all_level_params_defined_go(pers, st, params, memo, fuel, &t) {
                Err(e) => Err(e),
                Ok(b1) => {
                    if !b1 {
                        Ok(false)
                    } else {
                        match all_level_params_defined_go(pers, st, params, memo, fuel, &v) {
                            Err(e) => Err(e),
                            Ok(b2) => {
                                if !b2 {
                                    Ok(false)
                                } else {
                                    all_level_params_defined_go(pers, st, params, memo, fuel, &b)
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(ENodeView::Proj(_, _, e)) => all_level_params_defined_go(pers, st, params, memo, fuel, &e),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:218-255
/// allLevelParamsDefinedGo` — the twin's one `.lam | .forallE` clause, which
/// additionally reads the binder's `pw` datum.
pub fn all_level_params_defined_binder(
    pers: &PersTier,
    st: &AState,
    params: &Vec<Name>,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    t: &EIdx,
    b: &EIdx,
    m: &BinderMeta,
) -> Result<bool, CheckError> {
    match all_level_params_defined_go(pers, st, params, memo, fuel, t) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match all_level_params_defined_go(pers, st, params, memo, fuel, b) {
                    Err(e) => Err(e),
                    Ok(b2) => Ok(b2 && prop_when::params_defined(params, &m.pw)),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// The `.const` clause's `ls.all (Level.allParamsDefined params)`, as an index
/// recursion (§3.4 forbids the closure `List.all` takes).
pub fn all_params_defined_list(params: &Vec<Name>, ls: &Vec<Level>, i: usize) -> bool {
    if i >= ls.len() {
        true
    } else if level::all_params_defined(params, &ls[i]) {
        all_params_defined_list(params, ls, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:405-407 Expr.allLevelParamsDefinedFast
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:257-262 allLevelParamsDefined`
/// — the executed `allLevelParamsDefined`: one memoized DAG walk, at the
/// parameter list read back once.
pub fn all_level_params_defined(
    pers: &PersTier,
    st: &AState,
    lps: &Vec<NIdx>,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match read_names(pers, st, lps) {
        Err(err) => Err(err),
        Ok(ks) => {
            let mut memo: HashMap<EIdx, bool> = HashMap::new();
            all_level_params_defined_go(pers, st, &ks, &mut memo, CORE_WALK_FUEL, e)
        }
    }
}

// ---------------------------------------------------------------------------
// `constsResolve`, memoized (`CheckerBase.lean:234-286`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/DeclCheck.lean:37-58 Expr.constsResolveF
/// con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:275-313 constsResolveFGo` —
/// the memoized walk.  The four LEAF clauses are `arena::core`'s
/// `consts_resolve` at one node, exactly as con-leche's `…Go` calls the pure
/// walk at its four non-recursive constructors; everything else probes.
///
/// **Not the pure walk.**  Every declaration front door asks this of a stream
/// term, and on a DAG-shared type the pure walk unfolds the DAG (con-leche's
/// task #210 Part B, `tests/e2e/tower_struct.ndjson`; task #97d met the same
/// thing on eight fixtures and it is what made them time out).
pub fn consts_resolve_f_go(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CRF)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(ENodeView::Sort(_)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(ENodeView::Lit(_)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(ENodeView::Const(_, _)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(v) => match memo_b_get(memo, h) {
                Some(r) => Ok(r),
                None => match consts_resolve_f_node(pers, vis, st, fe, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        memo.insert(h.dup2(), r);
                        Ok(r)
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:275-313 constsResolveFGo` —
/// the six memoized arms, past the probe.  The `.proj` arm's `fe.find? s` is
/// the structure's own resolution, as the twin has it.
pub fn consts_resolve_f_node(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<bool, CheckError> {
    match v {
        ENodeView::FVar(_, ty) => consts_resolve_f_go(pers, vis, st, fe, memo, fuel, &ty),
        ENodeView::App(f, a) => consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &f, &a),
        ENodeView::Lam(ty, body, _) => consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &ty, &body),
        ENodeView::ForallE(ty, body, _) => consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &ty, &body),
        ENodeView::LetE(ty, val, body) => {
            match consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &ty, &val) {
                Err(e) => Err(e),
                Ok(b12) => match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, &body) {
                    Err(e) => Err(e),
                    Ok(b3) => Ok(b12 && b3),
                },
            }
        }
        ENodeView::Proj(s, _, sub) => match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, &sub) {
            Err(e) => Err(e),
            Ok(b) => Ok(ifenv_find(vis, fe, &s).is_some() && b),
        },
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
/// The twin's `(b₁ && b₂, memo)` of the two-child arms.  **Both children are
/// walked**, as the twin walks them: the conjunction is not short-circuited,
/// because the memo the second walk fills is part of the state.
pub fn consts_resolve_f_two(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, a) {
        Err(e) => Err(e),
        Ok(b1) => match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, b) {
            Err(e) => Err(e),
            Ok(b2) => Ok(b1 && b2),
        },
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:315-319 constsResolveFFast`
/// — the executed `constsResolve` (one memoized DAG walk), which is what every
/// front door below calls.
pub fn consts_resolve_f_fast(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    let mut memo: HashMap<EIdx, bool> = HashMap::new();
    consts_resolve_f_go(pers, vis, st, fe, &mut memo, CORE_WALK_FUEL, e)
}

/// con-leche: none — `xs.map Expr.fvarTypeD` over a list of handles
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:321-329 fvarTypeDs` — §3.4
/// forbids the closure `List.map` takes, and its rule for a `List` recursion
/// is a helper.
pub fn fvar_type_ds(
    pers: &PersTier,
    st: &AState,
    hs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= hs.len() {
        Ok(out)
    } else {
        match fvar_type_d(pers, st, &hs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut out2 = out;
                out2.push(t);
                fvar_type_ds(pers, st, hs, i + 1, out2)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// `mentionsConst` (module note 5)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:71-91 unresolvedConstsError
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:342-352 unresolvedConstsError`
/// — **the verdict at a term whose constants do not all resolve.**  A term that
/// mentions `sorryAx` DECLINES (the axiom is tolerated as a declaration and
/// installs nothing, so a use of it is a positively detected unsupported
/// feature); anything else is an unknown constant and REJECTS.  Monadic here
/// because the walk reads the store; the twin's `where_ : String` argument only
/// names the slot in the message, and §3.1 drops the interpolation.
pub fn unresolved_consts_error(
    pers: &PersTier,
    st: &mut AState,
    e: &EIdx,
) -> Result<CheckError, CheckError>  {
    match pin_sorry_ax(st) {
        Err(err) => Err(err),
        Ok(sa) => match crate::arena::inductives::struct_parts::mentions_const(pers, st, &sa, e) {
            Err(err) => Err(err),
            Ok(r) => {
                if r {
                    Ok(CheckError::NotImplemented(code_points(&M_SORRY)))
                } else {
                    Ok(CheckError::Invalid(code_points(&M_UNKNOWN_CONST)))
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The per-declaration constant check (`CheckerBase.lean:321-354`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:356-387 checkConstantVal` —
/// checks common to all declarations: fresh name, no reserved name, no
/// reserved projection shape, well-formed universe parameters, and a type that
/// is a type and mentions only declared parameters.  Returns the constant with
/// its type **annotated**; the guards run on the annotated type.
///
/// The twin reads the name back for four of the six messages (DESIGN.md §8.3's
/// "readback happens only for the environment index's error text"); the port
/// drops the interpolation, so the readbacks go with it.
pub fn check_constant_val(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<IConstantVal, CheckError> {
    match check_constant_val_guards(pers, vis, st, fe, cv) {
        Err(e) => Err(e),
        Ok(()) => match annotate_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &cv.ty) {
            Err(e) => Err(e),
            Ok(ty) => check_constant_val_after_annot(pers, vis, st, mode, fe, cv, ty),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:356-387 checkConstantVal` —
/// the six SYNTACTIC guards, in the twin's order.  Split off so the annotation
/// is a tail call and the guards do not join on a borrowed state; shared with
/// `arena::checker_split::install_constant_val`, which the twin writes out
/// clause for clause a second time (as con-leche does).
pub fn check_constant_val_guards(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    if ifenv_find(vis, fe, &cv.name).is_some() {
        fail(CheckError::Invalid(code_points(&M_DUP_DECL)))
    } else {
        match reserved_basis_names(st) {
            Err(e) => Err(e),
            Ok(rs) => {
                if nidx_contains_from(&rs, 0, &cv.name) {
                    fail(CheckError::Invalid(code_points(&M_RESERVED_BASIS)))
                } else {
                    check_constant_val_guards_rest(pers, st, cv)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:356-387 checkConstantVal` —
/// the four guards past the reserved-name test.
pub fn check_constant_val_guards_rest(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    match nidx_is_proj_fn_shape(pers, st, &cv.name) {
        Err(e) => Err(e),
        Ok(p) => {
            if p {
                fail(CheckError::Invalid(code_points(&M_RESERVED_PROJ)))
            } else if !name_nodup(&cv.level_params) {
                fail(CheckError::Invalid(code_points(&M_DUP_UNIV)))
            } else {
                match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, &cv.ty) {
                    Err(e) => Err(e),
                    Ok(b) => {
                        if !b {
                            fail(CheckError::Invalid(code_points(&M_LOOSE_TYPE)))
                        } else {
                            match has_fvar_fast(pers, st, CORE_WALK_FUEL, &cv.ty) {
                                Err(e) => Err(e),
                                Ok(f) => {
                                    if f {
                                        fail(CheckError::Invalid(code_points(&M_FVAR_TYPE)))
                                    } else {
                                        Ok(())
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:356-387 checkConstantVal` —
/// the tail past the annotation: the two guards on the ANNOTATED type, the
/// type's own sort, and the record update `{ cv with type := type }`.
pub fn check_constant_val_after_annot(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    ty: EIdx,
) -> Result<IConstantVal, CheckError> {
    match install_constant_val_tail(pers, vis, st, fe, cv, ty) {
        Err(e) => Err(e),
        Ok(cv_a) => match infer_type_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &cv_a.ty) {
            Err(e) => Err(e),
            Ok(stype) => match ensure_sort_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &stype) {
                Err(e) => Err(e),
                Ok(_u) => Ok(cv_a),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// con-leche: ConLeche/Kernel/CheckerSplit.lean:64-85 installConstantVal
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:356-387 checkConstantVal`
/// (and `CheckerSplit.lean:64-85 installConstantVal`, which spells it a second
/// time) — the two guards on the annotated type and the header they produce.
/// This is exactly the install half's tail, so the two twins share it here
/// where the Lean writes it twice.
pub fn install_constant_val_tail(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    ty: EIdx,
) -> Result<IConstantVal, CheckError> {
    match all_level_params_defined(pers, st, &cv.level_params, &ty) {
        Err(e) => Err(e),
        Ok(d) => {
            if !d {
                fail(CheckError::Invalid(code_points(&M_UNDECL_TYPE)))
            } else {
                match consts_resolve_f_fast(pers, vis, st, fe, &ty) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        if !r {
                            match unresolved_consts_error(pers, st, &ty) {
                                Err(e) => Err(e),
                                Ok(e) => fail(e),
                            }
                        } else {
                            Ok(IConstantVal {
                                name: cv.name.dup2(),
                                level_params: nidx_vec_dup(&cv.level_params),
                                ty,
                            })
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The strategy-independent helpers (`CheckerBase.lean:356-543`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
/// con-leche: ConLeche/Kernel/CheckerBase.lean:142-151 domsMatchAuxA
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:391-402 domsMatchAux` —
/// compare binder domains at offsets `o1`/`o2` for `n` positions, at the
/// IDENTITY view (module note 4).  con-leche's `List` version is quadratic on a
/// wide telescope and its `Array` twin is what the checker runs, so the twin is
/// the array one; and over handles a domain comparison is a handle comparison,
/// so this is PURE.
pub fn doms_match_aux(
    bs1: &Vec<(EIdx, BinderMeta)>,
    bs2: &Vec<(EIdx, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
) -> bool {
    doms_match_aux_from(bs1, bs2, o1, o2, n, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:142-151 domsMatchAuxA
/// The cited `(List.range n).all` as an index recursion, with the two `getD`
/// bound tests spelled out (the twin's `bs₁[o₁ + i]?` arms).
pub fn doms_match_aux_from(
    bs1: &Vec<(EIdx, BinderMeta)>,
    bs2: &Vec<(EIdx, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
    i: u64,
) -> bool {
    if i >= n {
        true
    } else {
        let j1: u64 = o1 + i;
        let j2: u64 = o2 + i;
        if j1 >= bs1.len() as u64 {
            false
        } else if j2 >= bs2.len() as u64 {
            false
        } else if bs1[j1 as usize].0.eq2(&bs2[j2 as usize].0) {
            doms_match_aux_from(bs1, bs2, o1, o2, n, i + 1)
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:404-420 openPisAtFvars` —
/// open the first `n` `∀`-binders at fresh free variables `0..n-1` (each
/// fvar's type is the binder domain, instantiated with the earlier fvars).
/// Structural on `n`, so no fuel of its own.
pub fn open_pis_at_fvars(
    pers: &PersTier,
    st: &mut AState,
    n: u64,
    h: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if n == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((dom, body, _)) => match intern_e_fvar(pers, st, i, dom) {
                    Err(e) => Err(e),
                    Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                        Err(e) => Err(e),
                        Ok(b) => match open_pis_at_fvars(pers, st, n - 1, &b, i + 1) {
                            Err(e) => Err(e),
                            Ok(Some((fvs, e2))) => Ok(Some((cons_eidx(&fv, &fvs), e2))),
                            Ok(None) => Ok(None),
                        },
                    },
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:422-439 openPisAtFvarsFGo` —
/// core of `openPisAtFvarsF`: `acc` holds the already-created fvars — the list
/// `instantiate_list` takes at cursor 0, in PUSH order on an OWNED vector
/// (task #97-P6-15).  One `instantiateList` pass per domain instead of one
/// whole-telescope `instantiate1` pass per binder.  The list this function
/// RETURNS is a different one and keeps its cons: it is built on the way out.
pub fn open_pis_at_fvars_f_go(
    pers: &PersTier,
    st: &mut AState,
    acc: Vec<EIdx>,
    n: u64,
    h: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if n == 0 {
        match instantiate_list_fast(pers, st, CORE_WALK_FUEL, h, &acc, 0) {
            Err(e) => Err(e),
            Ok(b) => Ok(Some((Vec::new(), b))),
        }
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((dom, body, _)) => {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &dom, &acc, 0) {
                        Err(e) => Err(e),
                        Ok(d) => match intern_e_fvar(pers, st, i, d) {
                            Err(e) => Err(e),
                            Ok(fv) => {
                                let mut acc2: Vec<EIdx> = acc;
                                acc2.push(fv.dup2());
                                match open_pis_at_fvars_f_go(pers, st, acc2, n - 1, &body, i + 1) {
                                    Err(e) => Err(e),
                                    Ok(Some((fvs, e2))) => Ok(Some((cons_eidx(&fv, &fvs), e2))),
                                    Ok(None) => Ok(None),
                                }
                            }
                        },
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:441-448 openPisAtFvarsF` —
/// one-pass `openPisAtFvars` (the fallback covers telescopes whose binders only
/// appear after substitution).  **The executed one.**
pub fn open_pis_at_fvars_f(
    pers: &PersTier,
    st: &mut AState,
    n: u64,
    e: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    match open_pis_at_fvars_f_go(pers, st, Vec::new(), n, e, i) {
        Err(err) => Err(err),
        Ok(Some(r)) => Ok(Some(r)),
        Ok(None) => open_pis_at_fvars(pers, st, n, e, i),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:450-461 checkTypedList` —
/// check each expression's inferred type against the corresponding expected
/// type (definitionally); throws on a length mismatch.  The cited two-`List`
/// recursion is one index recursion.
pub fn check_typed_list(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    ts: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= xs.len() && i >= ts.len() {
        Ok(())
    } else if i >= xs.len() || i >= ts.len() {
        fail(CheckError::NotImplemented(code_points(&M_NESTED_PIN_ARITY)))
    } else {
        match infer_type_core(pers, vis, st, mode, fe, CHECK_FUEL, depth, &xs[i]) {
            Err(e) => Err(e),
            Ok(ty) => match is_def_eq_core(pers, vis, st, mode, fe, CHECK_FUEL, depth, &ty, &ts[i]) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        check_typed_list(pers, vis, st, mode, fe, depth, xs, ts, i + 1)
                    } else {
                        fail(CheckError::NotImplemented(code_points(&M_NESTED_PIN_TYPE)))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:463-473 checkAnnotList` —
/// check that each expression is a fixed point of the annotation pass in the
/// given context.
pub fn check_annot_list(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= xs.len() {
        Ok(())
    } else {
        match annotate_core(pers, vis, st, mode, fe, CHECK_FUEL, depth, &xs[i]) {
            Err(e) => Err(e),
            Ok(a_a) => {
                if a_a.eq2(&xs[i]) {
                    check_annot_list(pers, vis, st, mode, fe, depth, xs, i + 1)
                } else {
                    fail(CheckError::NotImplemented(code_points(&M_NESTED_PIN_ANNOT)))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:208-211 isEqHead
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:475-484 isEqHead` — is the
/// expression the pinned equality former at one level?
pub fn is_eq_head(pers: &PersTier, st: &mut AState, h: &EIdx) -> Result<bool, CheckError> {
    if h.tag() == ETAG_CONST {
        match view_const(pers, st, h) {
            None => fail_dangling_e(),
            Some((c, us)) => match pin_eq(st) {
                Err(e) => Err(e),
                Ok(en) => {
                    if c.eq2(&en) {
                        match view_ls(pers, st, &us) {
                            Err(e) => Err(e),
                            Ok(l) => Ok(l.len() == 1),
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

/// con-leche: ConLeche/Kernel/CheckerBase.lean:213-220 eqHeadLevel
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:486-497 eqHeadLevel` — the
/// level an equality head carries.  Off shape it is `.zero`, which `isEqHead`
/// has already rejected wherever the result is used.
pub fn eq_head_level(pers: &PersTier, st: &mut AState, h: &EIdx) -> Result<LIdx, CheckError> {
    if h.tag() == ETAG_CONST {
        match view_const(pers, st, h) {
            None => fail_dangling_e(),
            Some((_, us)) => eq_head_level_at(pers, st, &us),
        }
    } else {
        zero_level(st)
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:213-220 eqHeadLevel
/// The cited `match ← viewLs us with | [l] => pure l | _ => zeroLevel`, as its
/// own function so the list's borrow ends before the state is taken mutably
/// again (task #97-P4c's extraction rule 5's reason).
pub fn eq_head_level_at(pers: &PersTier, st: &mut AState, us: &LsIdx) -> Result<LIdx, CheckError> {
    match view_ls(pers, st, us) {
        Err(e) => Err(e),
        Ok(l) => {
            if l.len() == 1 {
                Ok(l[0].dup2())
            } else {
                zero_level(st)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:499-509 checkDefEqList` —
/// pairwise definitional-equality check of two spines (throws on any mismatch,
/// including a length difference).
pub fn check_def_eq_list(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    ys: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= xs.len() && i >= ys.len() {
        Ok(())
    } else if i >= xs.len() || i >= ys.len() {
        fail(CheckError::NotImplemented(code_points(&M_IOTA_COMP_ARITY)))
    } else {
        match is_def_eq_core(pers, vis, st, mode, fe, CHECK_FUEL, depth, &xs[i], &ys[i]) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    check_def_eq_list(pers, vis, st, mode, fe, depth, xs, ys, i + 1)
                } else {
                    fail(CheckError::NotImplemented(code_points(
                        &M_IOTA_COMP_MISMATCH,
                    )))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:233-239 unwrapOr
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:511-516 unwrapOr` — unwrap
/// an optional value or fail with the given error.
pub fn unwrap_or<T>(o: Option<T>, err: CheckError) -> Result<T, CheckError> {
    match o {
        Some(a) => Ok(a),
        None => Err(err),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:241-247 Env.findCV?
/// con-leche: ConLeche/Kernel/DeclCheck.lean:33-35 FEnv.findCV?
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:518-524 IFEnv.findCV?` —
/// the stored constant under `n`, as an `IConstantVal`, if any.  The stored
/// constant is COPIED before the state is taken mutably (task #14's rule,
/// task #97-P4c's row).
pub fn ifenv_find_cv(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
) -> Result<Option<IConstantVal>, CheckError> {
    match ifenv_find(vis, fe, n) {
        Some(ci) => {
            let c = i_constant_info_dup(ci);
            match i_constant_info_to_constant_val(pers, &mut st.store, &c) {
                Err(e) => Err(e),
                Ok(cv) => Ok(Some(cv)),
            }
        }
        None => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:249-254 piResultSort
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:526-534 piResultSort` — the
/// result sort of a syntactic pi telescope, if it ends in a sort at all.
pub fn pi_result_sort(pers: &PersTier, st: &AState, e: &EIdx) -> Result<Option<LIdx>, CheckError> {
    match pi_result(pers, st, CORE_WALK_FUEL, e) {
        Err(err) => Err(err),
        Ok(r) => if r.tag() == ETAG_SORT {
            match view_sort(pers, st, &r) {
                None => fail_dangling_e(),
                Some(u) => Ok(Some(u)),
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:257-272 checkProjShape
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:536-552 checkProjShape` —
/// stage 2b: the projection type's parameter telescope is *syntactically* the
/// constructor's, and the constructor's residual is the family applied to
/// exactly the parameters.
pub fn check_proj_shape(
    pers: &PersTier,
    st: &AState,
    pty: &EIdx,
    ctor_ty: &EIdx,
    n_p: u64,
    n_f: u64,
) -> Result<(), CheckError> {
    match strip_pis(pers, st, n_p, pty) {
        Err(e) => Err(e),
        Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_TYPE_TELE))),
        Ok(Some(_)) => match strip_pis(pers, st, n_p + n_f, ctor_ty) {
            Err(e) => Err(e),
            Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_CTOR_TELE))),
            Ok(Some((_, cbody))) => check_proj_shape_residual(pers, st, &cbody, n_p),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:257-272 checkProjShape
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:536-552 checkProjShape` —
/// the residual's arity and head, past the two telescopes.
pub fn check_proj_shape_residual(
    pers: &PersTier,
    st: &AState,
    cbody: &EIdx,
    n_p: u64,
) -> Result<(), CheckError>  {
    match get_app_args(pers, st, CORE_WALK_FUEL, cbody) {
        Err(e) => Err(e),
        Ok(args) => {
            if args.len() as u64 != n_p {
                fail(CheckError::NotImplemented(code_points(&M_PROJ_CTOR_ARITY)))
            } else {
                match get_app_fn(pers, st, CORE_WALK_FUEL, cbody) {
                    Err(e) => Err(e),
                    Ok(f) => if f.tag() == ETAG_CONST {
                        match view_const_name(pers, st, &f) {
                            None => fail_dangling_e(),
                            Some(_) => Ok(()),
                        }
                    } else {
                        fail(CheckError::NotImplemented(code_points(&M_PROJ_CTOR_HEAD)))
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-590 checkProjRule` —
/// stage 3: the reduction rule — λ over the constructor telescope returning
/// field `i`, annotated; its λ-domains stay the constructor's.  The twin's one
/// `do` block is six functions here, split at its own `let`-boundaries
/// (task #97-P4c's rule).
pub fn check_proj_rule(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> Result<EIdx, CheckError> {
    match intern_e_bvar(pers, st, sub_nat(n_f, 1 + i)) {
        Err(e) => Err(e),
        Ok(bv) => match pis_to_lams(pers, st, n_p + n_f, &cvj.ty, &bv) {
            Err(e) => Err(e),
            Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_RULE_TELE))),
            Ok(Some(rhs)) => check_proj_rule_scoped(pers, vis, st, mode, fe, pty, cvj, lps, n_p, n_f, bv, rhs),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-590 checkProjRule` —
/// the raw rule's scoping guards and its annotation.  **Both guards are
/// computed**, as the twin's `unless !(← hasFvarFast …) && (← looseBVars…) do`
/// computes them (task #97-P4c's "Lean's `do` does not short-circuit").
pub fn check_proj_rule_scoped(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    bv: EIdx,
    rhs: EIdx,
) -> Result<EIdx, CheckError> {
    match has_fvar_fast(pers, st, CORE_WALK_FUEL, &rhs) {
        Err(e) => Err(e),
        Ok(f) => match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, &rhs) {
            Err(e) => Err(e),
            Ok(b) => {
                if f || !b {
                    fail(CheckError::NotImplemented(code_points(
                        &M_PROJ_RULE_SCOPING,
                    )))
                } else {
                    match annotate_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &rhs) {
                        Err(e) => Err(e),
                        Ok(rhs_a) => {
                            check_proj_rule_wf(pers, vis, st, mode, fe, pty, cvj, lps, n_p, n_f, bv, rhs_a)
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-590 checkProjRule` —
/// the annotated rule's well-formedness gate.
pub fn check_proj_rule_wf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    bv: EIdx,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match proj_rule_wf(pers, vis, st, fe, &rhs_a, lps) {
        Err(e) => Err(e),
        Ok(ok) => {
            if !ok {
                fail(CheckError::NotImplemented(code_points(&M_PROJ_RULE_WF)))
            } else {
                check_proj_rule_shape(pers, vis, st, mode, fe, pty, cvj, n_p, n_f, bv, rhs_a)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-590 checkProjRule` —
/// the cited `unless (← allLevelParamsDefined …) && (← constsResolveFFast …) &&
/// … do`: **all four are computed**, as the twin's `do` computes them, and the
/// conjunction is taken at the end.
pub fn proj_rule_wf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    rhs_a: &EIdx,
    lps: &Vec<NIdx>,
) -> Result<bool, CheckError> {
    match all_level_params_defined(pers, st, lps, rhs_a) {
        Err(e) => Err(e),
        Ok(d) => match consts_resolve_f_fast(pers, vis, st, fe, rhs_a) {
            Err(e) => Err(e),
            Ok(r) => match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, rhs_a) {
                Err(e) => Err(e),
                Ok(b) => match has_fvar_fast(pers, st, CORE_WALK_FUEL, rhs_a) {
                    Err(e) => Err(e),
                    Ok(f) => Ok(d && r && b && !f),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-590 checkProjRule` —
/// the syntactic stage past the annotation: the rule's λ telescope, its body
/// `bvar (nF - 1 - i)`, and its domains against the constructor's.
pub fn check_proj_rule_shape(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    bv: EIdx,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match strip_lams(pers, st, n_p + n_f, &rhs_a) {
        Err(e) => Err(e),
        Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_RULE_TELE))),
        Ok(Some((rbinders, rrbody))) => {
            if !rrbody.eq2(&bv) {
                fail(CheckError::NotImplemented(code_points(&M_PROJ_RULE_BODY)))
            } else {
                match strip_pis(pers, st, n_p + n_f, &cvj.ty) {
                    Err(e) => Err(e),
                    Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_CTOR_TELE))),
                    Ok(Some((cbinders_r, _))) => {
                        if !doms_match_aux(&rbinders, &cbinders_r, 0, 0, n_p + n_f) {
                            fail(CheckError::NotImplemented(code_points(&M_PROJ_RULE_DOMAIN)))
                        } else {
                            check_proj_rule_certs(pers, vis, st, mode, fe, pty, cvj, n_p, n_f, rhs_a)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// con-leche: ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-590 checkProjRule` —
/// the frame walks and the definitional parameter/domain pins, then the rule's
/// own inference.
pub fn check_proj_rule_certs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match open_pis_at_fvars_f(pers, st, n_p, pty, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_TYPE_TELE))),
        Ok(Some((fvs_p, _))) => match inst_pis_at_f(pers, st, CORE_WALK_FUEL, &fvs_p, &cvj.ty) {
            Err(e) => Err(e),
            Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_CTOR_TELE))),
            Ok(Some((cdoms_p, crest_p))) => match fvar_type_ds(pers, st, &fvs_p, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(ptypes) => {
                    match check_def_eq_list(pers, vis, st, mode, fe, n_p + n_f, &ptypes, &cdoms_p, 0) {
                        Err(e) => Err(e),
                        Ok(()) => {
                            check_proj_rule_frame(pers, vis, st, mode, fe, n_p, n_f, fvs_p, crest_p, rhs_a)
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-590 checkProjRule` —
/// the field frame, the λ-tower's instantiated domains, and the inference.
pub fn check_proj_rule_frame(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    n_f: u64,
    fvs_p: Vec<EIdx>,
    crest_p: EIdx,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match open_pis_at_fvars_f(pers, st, n_f, &crest_p, n_p) {
        Err(e) => Err(e),
        Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_CTOR_TELE))),
        Ok(Some((x_fvs, _))) => {
            let frame: Vec<EIdx> = append_eidx(fvs_p, &x_fvs);
            match inst_lams_at_f(pers, st, CORE_WALK_FUEL, &frame, &rhs_a) {
                Err(e) => Err(e),
                Ok(None) => fail(CheckError::NotImplemented(code_points(&M_PROJ_RULE_TELE))),
                Ok(Some((ldoms, _))) => match fvar_type_ds(pers, st, &frame, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(ftypes) => {
                        match check_def_eq_list(pers, vis, st, mode, fe, n_p + n_f, &ftypes, &ldoms, 0) {
                            Err(e) => Err(e),
                            Ok(()) => match infer_type_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &rhs_a) {
                                Err(e) => Err(e),
                                Ok(_rhs_ty) => Ok(rhs_a),
                            },
                        }
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The block's partition and its declared parameter count
// (`CheckerBase.lean:545-579` of the twin)
//
// Three `ConLeche/Kernel/Env.lean` declarations, placed at their only readers —
// the `.indDecl` arm and the modeled install — exactly as the six `Level.lean`
// declarations above are.  Task #97d-2 wrote them in
// `Arena/Inductives/Base.lean` under the concurrency contract; task #97f's
// dedup deleted that file and brought them here, and the Rust follows.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:716-719 ConstantInfo.isRecInfo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:600-604 isRecInfo` — is this
/// member a recursor record?
pub fn is_rec_info(ci: &IConstantInfo) -> bool {
    match ci {
        IConstantInfo::RecInfo(_, _, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:721-727 recsFormSuffix
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:606-612 recsFormSuffix` — do
/// the recursors form a suffix of the block?  The tag pass.  The cited `List`
/// recursion is an index recursion over the tail `block[i..]`.
pub fn recs_form_suffix(block: &Vec<IConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if is_rec_info(&block[i]) {
        all_rec_info(block, i + 1)
    } else {
        recs_form_suffix(block, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:721-727 recsFormSuffix
/// The cited `rest.all isRecInfo` (§3.4 forbids the closure `List.all` takes).
pub fn all_rec_info(block: &Vec<IConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if is_rec_info(&block[i]) {
        all_rec_info(block, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:588-622 indParamsOk
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:614-627 indParamsOk` —
/// **the stream's declared parameter count, checked as official checks it**
/// (con-leche's task #228).  Both halves are one-sided on purpose: `false`
/// means official rejects.
pub fn ind_params_ok(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    block: &Vec<IConstantInfo>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= block.len() {
        Ok(true)
    } else {
        match ind_params_ok_at(pers, st, n_p, &block[i]) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    ind_params_ok(pers, st, n_p, block, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:588-622 indParamsOk
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:614-627 indParamsOk` — one
/// member's test: a type former's Π-telescope is at least `nP` long, a
/// constructor's own parameter count is exactly `nP`, and everything else
/// passes.
pub fn ind_params_ok_at(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    ci: &IConstantInfo,
) -> Result<bool, CheckError>  {
    match ci {
        IConstantInfo::IndInfo(cv_t, _) => {
            match crate::arena::env::pi_sort_tele_len(pers, &st.store, CORE_WALK_FUEL, &cv_t.ty) {
                Err(e) => Err(e),
                Ok(Some(n)) => Ok(n_p <= n),
                Ok(None) => Ok(true),
            }
        }
        IConstantInfo::CtorInfo(_, n_pc, _) => Ok(*n_pc == n_p),
        _ => Ok(true),
    }
}
