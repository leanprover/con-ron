//! `ConLeche/Kernel/FEnv.lean`: the environment with a name index.
//!
//! The spec environment (`env::Env`) together with a `Name`-keyed index whose
//! lookup function agrees with `env::find`, built once per top-level entry
//! call.  Every index entry carries its **installation counter** — the number
//! of constants installed before it, i.e. its position counted from the
//! *bottom* of `env.consts` — and the record carries a **visibility bound**,
//! `visible_below`: `find` answers `None` for an entry whose counter is at or
//! above the bound, so a single `FEnv` value answers lookups against any
//! prefix of itself in `O(1)` (con-leche task #108).
//!
//! ## How `restrict_to` stays `O(1)` without Lean's persistence
//!
//! In the Lean, `restrictTo` is `{ fe with visibleBelow := k }` and `push` is
//! a three-field rebuild; both are `O(1)` because the runtime *shares* the
//! `Std.HashMap` field, and both leave the value they were given intact.  In
//! Rust there is no such sharing for free: a `&FEnv → FEnv` spelling would
//! have to copy the whole index.
//!
//! The port therefore takes **both by value and returns them** — the linear
//! threading task #6 established for accumulators (§3.4 reserves `&mut` for
//! the state parameter).  `restrict_to(fe, k)` is then literally the cited
//! record update: a move plus one field, `O(1)`, no clone, no `Rc`; `push(fe,
//! ci)` is the cited rebuild, `O(1)` amortised.  The *semantics* are the
//! Lean's exactly — `find(&restrict_to(fe, k), n)` is
//! `(fe.restrictTo k).find? n` — what changes is only that the caller no
//! longer holds the pre-restriction value, and must restore the bound
//! (`restrict_to(fe, full)`) rather than keep two views.
//!
//! **Why that is enough here** (DESIGN.md §1/§3.6, the two phases): phase A
//! installs, pushing; phase B checks, and takes `fe.restrictTo pc.vis` per
//! record.  In the Rust port phase A is *finished* before any check runs, so
//! the two operations never interleave, and phase B needs exactly one view at
//! a time — it lowers the bound for a record and raises it back.  The one
//! design this forecloses is the *parallel* phase B §3.1 contemplates, where
//! several workers hold different views of one index at once.  That is a
//! one-field change when it comes — `idx: Rc<HashMap<…>>`, with `push` moving
//! to an install-phase type that owns the map outright — and it does not
//! touch the model, because `abs` reads the index through `find` either way.
//!
//! ## What is *not* here
//!
//! `andRescueSlotsF` (`:102`) and the four indexed guard twins
//! `natLitSupportedF`, `strLitSupportedF`, `natOpGuardF`, `natOpStoredF`
//! (`:117-152`) read `andRescueSlotsOf`, `natIndOk`, `stringTyOk`, … and the
//! pinned basis names from `ConLeche/Kernel/Basis.lean` and
//! `ConLeche/Kernel/Core.lean`, neither of which is ported yet.  They are
//! this file's only omissions.

use crate::kernel::env;
use crate::kernel::env::ConstantInfo;
use crate::kernel::env::Env;
use crate::kernel::env::ProjEntry;
use crate::ron::hashmap::HashMap;
use crate::kernel::name::Name;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/FEnv.lean:44-49 FEnv
/// The spec environment together with a name index whose lookup function
/// agrees with `Env.find?`.  Deviations: `Std.HashMap` is `crate::ron::hashmap`
/// (§3.3), and the two `Nat`s — the per-entry installation counter and
/// `visibleBelow` — are `u64` (§3.3).
pub struct FEnv {
    pub env: Env,
    pub idx: HashMap<Name, (u64, ConstantInfo)>,
    /// Entries with counter `< visible_below` are visible; also the next
    /// counter `push` hands out.
    pub visible_below: u64,
}

/// con-leche: ConLeche/Kernel/FEnv.lean:56-60 mkFEnvGo
/// The index build, from the back: the newest (front) constant is inserted
/// last and wins, exactly as `List.find?` takes the first match — so the
/// agreement with `Env.find?` is unconditional (no freshness assumption).
/// The `u64` component is the running counter, so the build stays linear
/// (the tail's length is returned, not recomputed).
///
/// Deviation: the cited `List` recursion is the index recursion of task #3 —
/// `mk_fenv_go(cs, i)` is the cited function applied to `cs[i..]`, so the
/// entry point below passes `0`.
pub fn mk_fenv_go(cs: &Vec<ConstantInfo>, i: usize) -> (u64, HashMap<Name, (u64, ConstantInfo)>) {
    if i >= cs.len() {
        (0, HashMap::new())
    } else {
        let p = mk_fenv_go(cs, i + 1);
        let mut m = p.1;
        m.insert(
            env::constant_info_name(&cs[i]),
            (p.0, env::constant_info_dup(&cs[i])),
        );
        (p.0 + 1, m)
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:64-66 mkFEnv
/// Build the index of `env`, with nothing hidden (`visibleBelow` is the
/// constant count).  Takes the environment by value: the `FEnv` owns it.
pub fn mk_fenv(env: Env) -> FEnv {
    let p = mk_fenv_go(&env.consts, 0);
    FEnv {
        env,
        idx: p.1,
        visible_below: p.0,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:72-75 FEnv.find?
/// Indexed lookup, bounded by the visibility counter (`= Env.find?` for
/// `mk_fenv`, which hides nothing).
///
/// Deviation: a borrow rather than a copy of the stored record, as
/// `env::find` (task #9's "Lean's sharing costs a copy").
pub fn find<'a>(fe: &'a FEnv, n: &Name) -> Option<&'a ConstantInfo> {
    match fe.idx.get(n) {
        Some(e) => {
            if e.0 < fe.visible_below {
                Some(&e.1)
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:79-80 FEnv.restrictTo
/// Restrict the view to the first `k` installed constants.  `O(1)`: the
/// cited field update, with the record taken by value and returned (see the
/// module note on why that replaces Lean's persistence).
pub fn restrict_to(fe: FEnv, k: u64) -> FEnv {
    FEnv {
        env: fe.env,
        idx: fe.idx,
        visible_below: k,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:87-89 FEnv.push
/// The index of the cons-extended environment.  The new entry gets the next
/// installation counter, and the visibility bound advances with it — so a
/// push is visible to everything checked after it and to nothing checked
/// before (con-leche task #108).
///
/// Deviations: the record is taken by value and returned (the module note),
/// and `ci :: fe.env.consts` is `Vec::insert(0, ci)` — the port keeps
/// `Env.consts`' newest-first order, so the cons is a front insertion, `O(n)`
/// where Lean's is `O(1)`.  The environment list is *not* on any hot path:
/// every lookup goes through the index, and `consts` is read only by
/// `mk_fenv` and by the driver's final environment.  The constant is stored
/// twice (list and index) where Lean shares one value, hence the
/// `constant_info_dup`.
pub fn push(fe: FEnv, ci: ConstantInfo) -> FEnv {
    let mut consts = fe.env.consts;
    let mut idx = fe.idx;
    idx.insert(
        env::constant_info_name(&ci),
        (fe.visible_below, env::constant_info_dup(&ci)),
    );
    consts.insert(0, ci);
    FEnv {
        env: Env { consts },
        idx,
        visible_below: fe.visible_below + 1,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:92-95 FEnv.findProj?
/// Indexed projection-table lookup (`= Env.findProj?` for `mk_fenv`).
pub fn find_proj(fe: &FEnv, t: &Name, i: u64) -> Option<ProjEntry> {
    match find(fe, &env::proj_table_name(t)) {
        Some(ConstantInfo::ProjInfo(tbl)) => {
            if i < tbl.num_fields {
                Some(env::proj_table_entry(tbl, i))
            } else {
                None
            }
        }
        Some(_) => None,
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:98-99 FEnv.towerSlotsAllF
/// con-leche: ConLeche/Kernel/Core.lean:1000-1005 towerSlotsAll
/// `towerSlotsAll` through the index — and, since the port reads every
/// environment through the index (task #18's module note), *the* port of
/// `Core.lean`'s `towerSlotsAll` as well.
pub fn tower_slots_all_f(fe: &FEnv, t: &Name, n_f: u64) -> bool {
    tower_slots_all_f_from(fe, t, n_f, 0)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:98-99 FEnv.towerSlotsAllF
/// The index recursion the cited `(List.range nF).all` becomes (§3.4 forbids
/// closures); `j` runs `0 … nF-1` in the cited order.
pub fn tower_slots_all_f_from(fe: &FEnv, t: &Name, n_f: u64, j: u64) -> bool {
    if j >= n_f {
        true
    } else if find_proj(fe, t, j).is_some() {
        tower_slots_all_f_from(fe, t, n_f, j + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:106-110 FEnv.recSlotsAllF
/// con-leche: ConLeche/Kernel/Core.lean:1007-1015 recSlotsAll
/// `recSlotsAll` through the index — and the port of `Core.lean`'s
/// `recSlotsAll` (see `tower_slots_all_f`).
pub fn rec_slots_all_f(fe: &FEnv, t: &Name, n_f: u64) -> bool {
    rec_slots_all_f_from(fe, t, n_f, 0)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:106-110 FEnv.recSlotsAllF
/// The index recursion the cited `(List.range nF).all` becomes.
pub fn rec_slots_all_f_from(fe: &FEnv, t: &Name, n_f: u64, j: u64) -> bool {
    if j >= n_f {
        true
    } else if rec_slot_ok(fe, &env::proj_fn_name(t, j)) {
        rec_slots_all_f_from(fe, t, n_f, j + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:106-110 FEnv.recSlotsAllF
/// The cited body's one-slot test, as its own function so that the borrow of
/// the index ends before the recursion resumes; `env::is_rec_info` is the
/// cited `| some (.recInfo _ _ _ _) => true | _ => false`.
pub fn rec_slot_ok(fe: &FEnv, n: &Name) -> bool {
    match find(fe, n) {
        Some(ci) => env::is_rec_info(ci),
        None => false,
    }
}

/// con-leche: none — the `dup` of an `FEnv`; Lean's value semantics hides it
/// A full copy of the record, index included.  `O(size)`, so it is **not**
/// how a prefix view is taken — `restrict_to` is (see the module note).  It
/// exists because the differential harness (§3.6) wants to keep an
/// environment across a run, and the tests want two views alive at once.
///
/// The index is rebuilt with `mk_fenv_go` rather than copied entry by entry:
/// `crate::ron::hashmap` has no iteration API (by design — its module note), and
/// the rebuild is the definition of the counters anyway.  `visible_below` is
/// carried over unchanged, so a copy of a restricted view is that restricted
/// view.
pub fn dup(fe: &FEnv) -> FEnv {
    let p = mk_fenv_go(&fe.env.consts, 0);
    FEnv {
        env: env::env_dup(&fe.env),
        idx: p.1,
        visible_below: fe.visible_below,
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::env;
    use crate::kernel::env::ConstantInfo;
    use crate::kernel::env::ConstantVal;
    use crate::kernel::expr;
    use crate::kernel::fenv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn ax(s: &str) -> ConstantInfo {
        ConstantInfo::AxiomInfo(ConstantVal {
            name: nm(s),
            level_params: Vec::new(),
            ty: expr::sort(level::zero()),
        })
    }

    /// `mkFEnv` hides nothing, and its `find?` is `Env.find?`.
    #[test]
    fn mk_fenv_hides_nothing() {
        let e = env::Env {
            consts: vec![ax("c"), ax("b"), ax("a")],
        };
        let fe = fenv::mk_fenv(env::env_dup(&e));
        assert_eq!(fe.visible_below, 3);
        for n in ["a", "b", "c"] {
            assert_eq!(
                fenv::find(&fe, &nm(n)).is_some(),
                env::find(&e, &nm(n)).is_some()
            );
            assert!(fenv::find(&fe, &nm(n)).is_some());
        }
        assert!(fenv::find(&fe, &nm("z")).is_none());
        assert!(fenv::find(&fenv::mk_fenv(env::empty()), &nm("a")).is_none());
    }

    /// A push is visible to everything checked after it and to nothing
    /// checked before (`FEnv.push`, con-leche task #108).
    #[test]
    fn push_then_restrict_is_the_prefix_view() {
        // install a, then b, then c
        let fe = fenv::mk_fenv(env::empty());
        let fe = fenv::push(fe, ax("a"));
        let fe = fenv::push(fe, ax("b"));
        let fe = fenv::push(fe, ax("c"));
        assert_eq!(fe.visible_below, 3);
        // `consts` is newest first
        assert!(name::beq(
            &env::constant_info_name(&fe.env.consts[0]),
            &nm("c")
        ));
        assert!(name::beq(
            &env::constant_info_name(&fe.env.consts[2]),
            &nm("a")
        ));
        // and `mkFEnv_push`: pushing onto the index is building it afresh
        let fresh = fenv::mk_fenv(env::env_dup(&fe.env));
        assert_eq!(fresh.visible_below, fe.visible_below);
        for n in ["a", "b", "c", "z"] {
            assert_eq!(
                fenv::find(&fe, &nm(n)).is_some(),
                fenv::find(&fresh, &nm(n)).is_some()
            );
        }
        // the prefix views
        let v2 = fenv::restrict_to(fenv::dup(&fe), 2);
        assert!(fenv::find(&v2, &nm("a")).is_some());
        assert!(fenv::find(&v2, &nm("b")).is_some());
        assert!(fenv::find(&v2, &nm("c")).is_none());
        let v0 = fenv::restrict_to(fenv::dup(&fe), 0);
        assert!(fenv::find(&v0, &nm("a")).is_none());
        assert!(fenv::find(&v0, &nm("c")).is_none());
        // restoring the bound restores the view (the phase-B idiom)
        let back = fenv::restrict_to(v0, 3);
        assert!(fenv::find(&back, &nm("a")).is_some());
        assert!(fenv::find(&back, &nm("c")).is_some());
        // `dup` preserves the bound and every answer
        let d = fenv::dup(&v2);
        assert_eq!(d.visible_below, 2);
        assert!(fenv::find(&d, &nm("b")).is_some());
        assert!(fenv::find(&d, &nm("c")).is_none());
    }

    /// The newest binding of a name wins, in the index as in the list.
    #[test]
    fn shadowing_agrees_with_env_find() {
        let fe = fenv::mk_fenv(env::empty());
        let fe = fenv::push(fe, ax("x"));
        let fe = fenv::push(
            fe,
            ConstantInfo::ThmInfo(
                ConstantVal {
                    name: nm("x"),
                    level_params: Vec::new(),
                    ty: expr::sort(level::zero()),
                },
                expr::bvar(0),
            ),
        );
        // the index's entry is the newest, exactly as `List.find?` takes the
        // first match of the newest-first list
        match fenv::find(&fe, &nm("x")) {
            Some(ConstantInfo::ThmInfo(_, _)) => (),
            _ => panic!("the index kept the older binding"),
        }
        match env::find(&fe.env, &nm("x")) {
            Some(ConstantInfo::ThmInfo(_, _)) => (),
            _ => panic!("the list kept the older binding"),
        }
        // ... and the older one is what the prefix view sees
        let v1 = fenv::restrict_to(fenv::dup(&fe), 1);
        match fenv::find(&v1, &nm("x")) {
            None => (),
            _ => panic!("the shadowed entry's counter is 1, so it is hidden"),
        }
    }

    #[test]
    fn proj_and_slot_queries() {
        let t = nm("S");
        let tbl = env::ProjTable {
            struct_name: name::dup(&t),
            level_params: Vec::new(),
            num_params: 0,
            ctor: nm("S.mk"),
            num_fields: 2,
            struct_sort: level::zero(),
            bodies: vec![expr::bvar(0), expr::bvar(1)],
            guards: vec![level::zero(), level::zero()],
            off: 0,
        };
        let fe = fenv::mk_fenv(env::empty());
        let fe = fenv::push(fe, ConstantInfo::ProjInfo(tbl));
        assert!(fenv::find_proj(&fe, &t, 0).is_some());
        assert!(fenv::find_proj(&fe, &t, 1).is_some());
        assert!(fenv::find_proj(&fe, &t, 2).is_none());
        assert!(fenv::tower_slots_all_f(&fe, &t, 2));
        assert!(!fenv::tower_slots_all_f(&fe, &t, 3));
        assert!(fenv::tower_slots_all_f(&fe, &t, 0));
        // no `projFnName` recursors are installed
        assert!(!fenv::rec_slots_all_f(&fe, &t, 1));
        assert!(fenv::rec_slots_all_f(&fe, &t, 0));
        let fe = fenv::push(
            fe,
            ConstantInfo::RecInfo(
                ConstantVal {
                    name: env::proj_fn_name(&t, 0),
                    level_params: Vec::new(),
                    ty: expr::sort(level::zero()),
                },
                0,
                0,
                Vec::new(),
            ),
        );
        assert!(fenv::rec_slots_all_f(&fe, &t, 1));
        assert!(!fenv::rec_slots_all_f(&fe, &t, 2));
    }
}
