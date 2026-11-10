//! `arena::checker` — the check phase's sequential pieces, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Checker.lean`.  con-leche's driver is
//! the parse, then the check (`ConLeche/Cached/StreamIndex.lean`,
//! `ConLeche/Driver/CheckPool.lean`): the stream's index is built from the
//! records alone (`arena::stream_index::build_index`), frozen, and every
//! record's check is a JOB at the index's view of its position
//! (`stream_index::record_job`), run on a pool of workers, the first failure in
//! fold order the verdict.  There is no install phase.  Everything sequential
//! of that is here, in the verified crate; the threads are
//! `crates/con-ron/src/pool.rs`'s:
//!
//! ```text
//!   intern_all_pins   the pinned data, interned once into the persistent tier
//!   build_index       (stream_index) the index, on the driver's store
//!   freeze_tier       the boundary: the persistent tier and the index move out
//!   worker_state      a worker's start state over the frozen tier
//!   run_job           one job, its error tagged with its position
//!   thaw_tier         the boundary undone
//! ```
//!
//! ## Every job is bracketed
//!
//! DESIGN.md §8.3: "Persistent = parse + the stream's index; scratch = one
//! declaration's check."  `record_job` empties the scratch tier, the memos and
//! the caches before and after the record's check (`enter_record`,
//! `leave_record`), so a worker's state between two jobs holds nothing of the
//! first but capacity, and nothing a job builds outlives it.
//!
//! ## The pins are interned at startup
//!
//! `intern_all_pins` is DESIGN.md §8.6 P2d's one-time tree walk, and it is what
//! makes every later `pin`/`intern_ci` of the same datum return the PERSISTENT
//! handle whatever tier is live (§8.3: `intern` probes the persistent table
//! first).  Without it a reserved name first interned inside a scratch tier
//! would compare unequal to the stream's own persistent copy of it, which is
//! the one way hash-consing can go wrong across the tier boundary.

use crate::arena::basis::basis_kind_decls;
use crate::arena::core::{nat_div_mod_names, nat_op_names};
use crate::arena::env::{nidx_vec_dup, IDeclaration};
use crate::arena::monad::AState;
use crate::arena::nat_op_pin_set::{intern_pin_sets, INatOpPinSet};
use crate::arena::pins::{pin_quot_sound, pin_sorry_ax, Pins};
use crate::arena::store::{EStore, ETables, LTables, LsTables, NTables, PersTier};
use crate::arena::stream_index::{record_job, IStreamIndex};
use crate::arena::trust_axioms::reduce_op_names;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::{BasisKind, CheckMode};
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::ron::hashmap::Dup;
use crate::ron::nat::{self, Nat};

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"check phase: no job"`, as code points — the cited message with the
/// position dropped (§3.1); the error carries the position.
pub const M_NO_JOB: [u32; 19] = [
    99, 104, 101, 99, 107, 32, 112, 104, 97, 115, 101, 58, 32, 110, 111, 32, 106, 111, 98
];

// ---------------------------------------------------------------------------
// The phase boundary and a worker (task #97-P5-Driver)
// ---------------------------------------------------------------------------

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the twin has no tier to move; its worker reads the
/// persistent tier where it is (`AState.worker`, `Arena/Checker.lean`).
/// **The persistent tier and the stream's index into a value**: the four
/// persistent tables and the index move into one `PersTier` handed back
/// `frozen`, for the workers to read (the index is the base `ifenv_find` reads
/// below a job's own layer).  A pure MOVE: the store's scratch tiers and flags
/// are untouched (a worker's store is its own, `worker_state`), and
/// `thaw_tier` puts everything back where it was.  The driver's store is not
/// read between the two.
pub fn freeze_tier(ar: &mut EStore, ix: IStreamIndex) -> PersTier {
    let n: NTables = core::mem::replace(&mut ar.lss.ls.ns.pers, NTables::empty());
    let l: LTables = core::mem::replace(&mut ar.lss.ls.pers, LTables::empty());
    let ls: LsTables = core::mem::replace(&mut ar.lss.pers, LsTables::empty());
    let e: ETables = core::mem::replace(&mut ar.pers, ETables::empty());
    PersTier {
        frozen: true,
        n,
        l,
        ls,
        e,
        env: ix,
    }
}

/// con-leche: none — the phase boundary, which con-leche has no tier to make
/// Lean twin: none — the inverse of `freeze_tier`, which has none either.
/// **`freeze_tier` inverted**: the tables back into the store and the index back
/// to the caller, so that everything after the check phase — the verdict line's
/// label, the failing record's name — reads the handles it was given.
/// `thaw_tier(ar, freeze_tier(ar, ix))` leaves the store exactly as it found it
/// and answers `ix`.
pub fn thaw_tier(ar: &mut EStore, tier: PersTier) -> IStreamIndex {
    ar.lss.ls.ns.pers = tier.n;
    ar.lss.ls.pers = tier.l;
    ar.lss.pers = tier.ls;
    ar.pers = tier.e;
    tier.env
}

/// con-leche: none — the pin table is handles, so a copy is a copy of words
/// Lean twin: none — the value is `Pins` itself (`Refine2`'s `pins_dup_val`).
/// A worker's copy of the driver's `Pins`: handles into the frozen tier and
/// nothing else, so every worker's state may own one and none of them has to
/// intern anything to fill it.
pub fn pins_dup(p: &Pins) -> Pins {
    Pins {
        names: nidx_vec_dup(&p.names),
        reserved: nidx_vec_dup(&p.reserved),
        empty_levels: p.empty_levels.dup2(),
        zero_level: p.zero_level.dup2(),
        sort_one: p.sort_one.dup2(),
        max_nat_size: nat::clone(&p.max_nat_size),
    }
}

/// con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool
/// con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove checker::worker_state_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Checker.lean:64-71 AState.worker` — the twin's
/// worker reads the persistent tier where it is.
/// **A worker's start state** (the cited `init`): the empty store, FROZEN
/// (`EStore::empty_frozen`, task #98-FREEZE), so that every persistent read goes
/// to the `PersTier` the boundary froze and every append is a scratch append;
/// fresh memos and caches; and a copy of the pins.  The store stays frozen for
/// the worker's life: `record_job` only empties its scratch tier.
pub fn worker_state(pins: &Pins) -> AState {
    let mut st = AState::init(EStore::empty_frozen());
    st.pins = pins_dup(pins);
    st
}

/// con-leche: ConLeche/Driver/CheckPool.lean:116-123 runAt
/// con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove checker::run_job_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Checker.lean:73-83 runJob` — **job `k`, run**: the
/// record's job at its position (`stream_index::record_job`), a failure tagged
/// with that position.  A position past the records is an internal error, never
/// a verdict.
pub fn run_job(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    k: u64,
) -> Result<(), (CheckError, u64)> {
    if (k as usize) < ds.len() {
        match record_job(pers, st, mode, pins, k, &ds[k as usize]) {
            Err(e) => Err((e, k)),
            Ok(()) => Ok(()),
        }
    } else {
        Err((CheckError::Internal(code_points(&M_NO_JOB)), k))
    }
}

// ---------------------------------------------------------------------------
// The startup walk (`Checker.lean:343-373` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// con-leche: ConLeche/Kernel/Basis.lean:39-45 BasisKind.decls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — **the
/// one-time tree walk of DESIGN.md §8.6 P2d**: every datum the checker compares
/// a stream record against, interned into the tier that is live at the call —
/// which, at the driver's call, is the persistent one.
///
/// The five basis blocks' pins (what a basis block's and a quotient record's
/// job compares the record with), the standard and compiler-trust axiom pins, the reserved names
/// the guards compare by handle, and the `Nat`-operation pin variants, whose
/// interned form is the checker's pin-list parameter (con-leche's task #304).
/// First, the run's maximum `Nat` size goes into the pin record
/// (`Pins::max_nat_size`): con-leche threads it beside the pin list
/// (`checkDecls mode pins maxNatSize`) into every declaration's fresh state
/// (`{ maxNatSize := maxNatSize }`, `Cached.declStep`, `Cached.recordJob`); here
/// every worker copies it with the pins (`worker_state`) and no job writes it.
pub fn intern_all_pins(
    pers: &PersTier,
    st: &mut AState,
    pins: &Vec<NatOpPinSet>,
    max_nat_size: &Nat,
) -> Result<Vec<INatOpPinSet>, CheckError> {
    st.pins.max_nat_size = nat::clone(max_nat_size);
    match intern_all_basis(pers, st, 0) {
        Err(e) => Err(e),
        Ok(()) => match intern_all_axiom_pins(pers, st) {
            Err(e) => Err(e),
            Ok(()) => match intern_all_names(st) {
                Err(e) => Err(e),
                Ok(()) => intern_pin_sets(pers, st, pins, 0, Vec::new()),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:39-45 BasisKind.decls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — the five
/// basis blocks in both forms, as a cursor over
/// `con_ron_core::kernel::basis_raw::block_pin_kinds` plus `quotK` (the twin
/// spells the twelve calls out).
pub fn intern_all_basis(pers: &PersTier, st: &mut AState, i: usize) -> Result<(), CheckError> {
    let ks: Vec<BasisKind> = all_basis_kinds();
    if i >= ks.len() {
        Ok(())
    } else {
        match basis_kind_decls(pers, st, &ks[i]) {
            Err(e) => Err(e),
            Ok(_) => intern_all_basis(pers, st, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:39-45 BasisKind.decls
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — the five
/// kinds the startup walk interns, in the twin's order.
pub fn all_basis_kinds() -> Vec<BasisKind> {
    let mut ks: Vec<BasisKind> = Vec::with_capacity(5);
    ks.push(BasisKind::EqK);
    ks.push(BasisKind::NatK);
    ks.push(BasisKind::EmptyK);
    ks.push(BasisKind::FalseK);
    ks.push(BasisKind::QuotK);
    ks
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — the
/// standard and compiler-trust axiom pins, in the twin's order.
pub fn intern_all_axiom_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::iff_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::iff_intro_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::iff_rec_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::nonempty_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_axiom_pins_rest(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — the
/// rest of the axiom pins and the two reduce pins.
pub fn intern_all_axiom_pins_rest(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::std_axioms::nonempty_intro_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::std_axioms::nonempty_rec_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::std_axioms::propext_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::std_axioms::choice_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_trust_pins(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — the
/// compiler-trust shapes and the two reduce pins.
pub fn intern_all_trust_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::trust_axioms::true_cv_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::trust_axioms::true_intro_cv_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::trust_axioms::trust_compiler_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::trust_axioms::bool_cv_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => intern_all_reduce_pins(pers, st),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — the
/// four `reduce*`/`ofReduce*` shapes and the two pinned defining expressions.
pub fn intern_all_reduce_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::trust_axioms::reduce_nat_cv_a(pers, st) {
        Err(e) => Err(e),
        Ok(_) => match crate::arena::trust_axioms::reduce_bool_cv_a(pers, st) {
            Err(e) => Err(e),
            Ok(_) => match crate::arena::trust_axioms::of_reduce_nat_a(pers, st) {
                Err(e) => Err(e),
                Ok(_) => match crate::arena::trust_axioms::of_reduce_bool_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(_) => match crate::arena::trust_axioms::reduce_nat_decl_pin(pers, st) {
                        Err(e) => Err(e),
                        Ok(_) => match crate::arena::trust_axioms::reduce_bool_decl_pin(pers, st)
                        {
                            Err(e) => Err(e),
                            Ok(_) => Ok(()),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/Checker.lean:124-153 internAllPins` — the
/// reserved names the guards compare by handle.
pub fn intern_all_names(st: &mut AState) -> Result<(), CheckError> {
    match crate::arena::core::reserved_basis_names(st) {
        Err(e) => Err(e),
        Ok(_) => match nat_op_names(st) {
            Err(e) => Err(e),
            Ok(_) => match nat_div_mod_names(st) {
                Err(e) => Err(e),
                Ok(_) => match reduce_op_names(st) {
                    Err(e) => Err(e),
                    Ok(_) => match pin_sorry_ax(st) {
                        Err(e) => Err(e),
                        Ok(_) => match pin_quot_sound(st) {
                            Err(e) => Err(e),
                            Ok(_) => Ok(()),
                        },
                    },
                },
            },
        },
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::pins::max_nat_size_default;

    /// con-leche: none — a test fixture
    /// The state the driver builds: an empty store with the reserved-name
    /// pins interned (task #97-P6-4a).  Every subject below reads a pin
    /// somewhere, so this is the only state they can run in.
    fn pinned_state() -> AState {
        let pers: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        match crate::arena::pins::intern_reserved_pins(pers, &mut st) {
            Ok(()) => st,
            Err(_) => panic!("the reserved-name pins must intern"),
        }
    }
    use crate::arena::intern::{intern_ci_list, intern_cv};
    use crate::arena::std_axioms::i_constant_val_matches_pin;
    use crate::arena::store::EStore;
    use crate::arena::env::IFEnv;
    use crate::kernel::basis_names;
    use crate::kernel::basis_raw;

    use crate::kernel::env::{ConstantInfo, ConstantVal};
    use crate::kernel::expr;
    use crate::kernel::expr::Expr;

    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::std_axioms as cstd;

    // --- the mode, the pins, and the outcome comparisons ---------------------

    /// The empty pin list, which is what `CheckerTest.lean` passes: no subject
    /// below reaches the `Nat.div`/`Nat.mod` variant loop with its guards
    /// passing, so the list's contents are not what is under test.
    fn no_pins() -> Vec<NatOpPinSet> {
        Vec::new()
    }

    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the fixture must build without a decline"),
        }
    }

    // --- the three runs ------------------------------------------------------

    // --- the subjects, written once as con-ron-core values -------------------

    fn nm(s: &str) -> Name {
        name::mk_str(name::anonymous(), s.chars().map(|c| c as u32).collect())
    }

    fn nat_ty() -> Expr {
        expr::mk_const(basis_names::nat_name(), Vec::new())
    }

    fn cv(n: Name, lps: Vec<Name>, ty: Expr) -> ConstantVal {
        ConstantVal { name: n, level_params: lps, ty }
    }

    // --- the lists -----------------------------------------------------------

    // --- what con-ron-core itself says ---------------------------------------

    // --- the differential: `check_decls_pure` --------------------------------

    // --- the differential: `check_decl` at a non-empty environment ------------

    // --- the differential: the TWO-PHASE fold --------------------------------

    // --- the pieces below `check_decl` ---------------------------------------

    /// An environment holding the `Eq` and `Nat` pins, built directly rather
    /// than by running a checker: a pinned block at the pin's own names installs
    /// the pin, pushed in order.
    fn basis_consts() -> Vec<ConstantInfo> {
        let mut cs: Vec<ConstantInfo> = Vec::new();
        for k in [BasisKind::EqK, BasisKind::NatK] {
            let mut b = basis_raw::basis_kind_decls(&k);
            while b.len() > 0 {
                cs.push(b.remove(0));
            }
        }
        cs
    }

    /// The arena's `std_axiom_ok` of `c` in the basis environment.
    fn std_axiom(c: &ConstantVal) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let cs = ok(intern_ci_list(pers, &mut st, &basis_consts()));
        let icv = ok(intern_cv(pers, &mut st, c));
        let mut fe: IFEnv = crate::arena::env::ifenv_layer(0, 0);
        let mut i: usize = 0;
        while i < cs.len() {
            fe = crate::arena::env::ifenv_push(fe, crate::arena::env::i_constant_info_dup(&cs[i]));
            i += 1;
        }
        ok(crate::arena::decl_check::std_axiom_ok(pers, &mut st, &fe, &icv))
    }

    /// The expected answers are what the `Expr`-tree reference implementation
    /// (`kernel::std_axioms`, deleted by task #105) gave on the same inputs,
    /// which this test used to compare against.
    #[test]
    fn std_axiom_ok_answers() {
        assert_eq!(std_axiom(&cv(cstd::propext_name(), Vec::new(), expr::sort(level::zero()))), false);
        assert_eq!(std_axiom(&cv(cstd::choice_name(), Vec::new(), expr::sort(level::zero()))), false);
        assert_eq!(std_axiom(&cv(nm("x"), Vec::new(), nat_ty())), false);
    }

    /// The arena's `matchesPin`.
    fn matches_pin(c: &ConstantVal, pin: &ConstantVal) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let a = ok(intern_cv(pers, &mut st, c));
        let b = ok(intern_cv(pers, &mut st, pin));
        i_constant_val_matches_pin(&a, &b)
    }

    /// On an identical term, one that differs in its type, one that differs
    /// in a binder's codomain, and one that differs in its level parameters.  Expected answers as in
    /// `std_axiom_ok_answers`.
    #[test]
    fn matches_pin_answers() {
        let two = nm("two");
        assert_eq!(matches_pin(
            &cv(name::dup(&two), Vec::new(), nat_ty()),
            &cv(name::dup(&two), Vec::new(), nat_ty())
        ), true);
        assert_eq!(matches_pin(
            &cv(name::dup(&two), Vec::new(), nat_ty()),
            &cv(name::dup(&two), Vec::new(), expr::sort(level::zero()))
        ), false);
        assert_eq!(matches_pin(
            &cv(name::dup(&two), Vec::new(), expr::forall_e(nat_ty(), nat_ty())),
            &cv(name::dup(&two), Vec::new(), expr::forall_e(nat_ty(), nat_ty()))
        ), true);
        assert_eq!(matches_pin(
            &cv(name::dup(&two), Vec::new(), expr::forall_e(nat_ty(), nat_ty())),
            &cv(
                name::dup(&two),
                Vec::new(),
                expr::forall_e(nat_ty(), expr::sort(level::zero()))
            )
        ), false);
        let mut lps: Vec<Name> = Vec::with_capacity(1);
        lps.push(nm("u"));
        assert_eq!(matches_pin(
            &cv(name::dup(&two), lps, nat_ty()),
            &cv(name::dup(&two), Vec::new(), nat_ty())
        ), false);
    }

    /// The arena's `canonEqList`.
    fn canon_list(xs: &Vec<ConstantInfo>, ys: &Vec<ConstantInfo>) -> bool {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let a = ok(intern_ci_list(pers, &mut st, xs));
        let b = ok(intern_ci_list(pers, &mut st, ys));
        ok(crate::arena::canon::canon_eq_list(pers, &mut st, &a, &b, 0))
    }

    /// On the pinned blocks and on a block that is not one.  Expected answers
    /// as in `std_axiom_ok_answers`.
    #[test]
    fn canon_eq_list_answers() {
        let nat = basis_raw::basis_kind_decls(&BasisKind::NatK);
        let eq = basis_raw::basis_kind_decls(&BasisKind::EqK);
        assert_eq!(canon_list(&nat, &basis_raw::basis_kind_decls(&BasisKind::NatK)), true);
        assert_eq!(canon_list(&eq, &basis_raw::basis_kind_decls(&BasisKind::EqK)), true);
        assert_eq!(canon_list(&eq, &nat), false);
    }

    // --- the startup walk and `atDecl` ---------------------------------------

    /// `intern_all_pins` puts every pinned datum in the PERSISTENT tier, which
    /// is what makes a later `pin` of the same name — inside a scratch tier —
    /// hand back the persistent handle.  Beyond the twin's `#guard`s: the Lean
    /// tests this from outside, through `chkInstall`'s readback.
    #[test]
    fn the_startup_walk_interns_into_the_persistent_tier() {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned_state();
        let _ = ok(intern_all_pins(pers, &mut st, &no_pins(), &max_nat_size_default()));
        let n0 = st.store.pers_count(pers);
        assert!(n0 > 0);
        // a worker over the frozen tier, and the same names again: nothing new
        // is appended and every handle is persistent
        let tier = freeze_tier(&mut st.store, crate::arena::stream_index::stream_index_empty());
        let mut w = worker_state(&st.pins);
        let eqn = ok(crate::arena::monad::intern_name(&tier, &mut w, &basis_names::eq_name()));
        assert!(eqn.is_persistent());
        let blk = ok(basis_kind_decls(&tier, &mut w, &BasisKind::EqK));
        let mut i: usize = 0;
        while i < blk.len() {
            let cvv = crate::arena::env::i_constant_info_to_constant_val(&blk[i]);
            assert!(cvv.ty.is_persistent());
            i += 1;
        }
        assert_eq!(w.store.pers_count(&tier), n0);
        let _ = thaw_tier(&mut st.store, tier);
    }

    /// **The startup walk at the binary's own pin list**, not the empty one
    /// every check above runs with: the embedded `con-ron-pins/2` text
    /// (`kernel::pins_text::PINS_TEXT`, 26 721 records) decoded and interned
    /// into the persistent tier.  This is the path `run_pipeline` takes and the
    /// one thing about it that could fail quietly — the handle-index cap, or a
    /// fresh-memo walk that does not finish.
    ///
    /// It runs on a 1 GB stack for `pins_decode`'s own reason (it recurses once
    /// per record), which is what the driver gives its checker threads anyway.
    #[test]
    fn the_startup_walk_interns_the_embedded_pins() {
        let h = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(|| {
                let pers: &PersTier = &PersTier::empty();
                let pins = match crate::kernel::pins_decode::decode_embedded() {
                    Ok(v) => v,
                    Err(_) => panic!("the embedded pin text must decode"),
                };
                assert!(pins.len() > 0);
                let mut st = pinned_state();
                let ip = ok(intern_all_pins(pers, &mut st, &pins, &max_nat_size_default()));
                assert_eq!(ip.len(), pins.len());
                // every interned pin is a PERSISTENT handle — the startup walk
                // runs before the first `enter_scratch`, which is what makes a
                // later `intern` of the same node hand the persistent one back
                let mut i: usize = 0;
                while i < ip.len() {
                    assert!(ip[i].div_pin.is_persistent());
                    assert!(ip[i].mod_pin.is_persistent());
                    assert!(ip[i].div_proofs.len() > 0);
                    i += 1;
                }
                st.store.node_count(pers)
            })
            .unwrap()
            .join()
            .unwrap();
        assert!(h > 0);
    }
}
