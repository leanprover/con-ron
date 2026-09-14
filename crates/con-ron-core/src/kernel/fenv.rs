//! `ConLeche/Kernel/FEnv.lean`: the environment with a name index.
//!
//! The spec environment (`env::Env`) together with a `Name`-keyed index whose
//! lookup function agrees with `env::find`, built once per top-level entry
//! call.  Every index entry carries its **installation counter** — the number
//! of constants installed before it, i.e. its index into `env.consts`, which
//! the port stores oldest-first (`env::Env`'s deviation, task #50) — and the
//! record carries a **visibility bound**,
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
//! record update: a move plus one field, `O(1)`, no clone, no handle bump; `push(fe,
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
//! several workers hold different views of one index at once.
//!
//! ## What `dup` costs, and why the index is not `P<HashMap>` (task #34)
//!
//! The one place a *second* view is unavoidable is the inductive install
//! routes, which hold two or three views of one index at once
//! (`inductives::native_install`, `inductives::modeled`); they take `dup`,
//! which rebuilds the index with `mk_fenv_go`.  Task #34 measured what that
//! costs and what the alternatives cost:
//!
//! * `Init` takes 1 000-odd `dup`s over 7.8 M index entries, against **80 M
//!   `find`s**.  Any *shared* index — `P<HashMap<…>>` with a copy on push, an
//!   overlay chain, a persistent trie — pays on `find` (a deeper probe, at
//!   80 M calls) more than it saves on `dup` (7.8 M entries); and `P`'s
//!   allowed API (§3.2: `new`/`clone`/`deref`/`ptr_eq`, no `make_mut`) has no
//!   way to extend a shared map in place at all.  `find` being ten times the
//!   traffic is why the flat owned map stays.
//! * What task #34 did instead is make the copied entry cheap: the stored
//!   record is **shared** (`P<ConstantInfo>`, `env::Env`'s deviation), so
//!   `push` and `mk_fenv_go` bump a pointer where they copied a record and
//!   the index no longer holds a second copy of the whole environment; and
//!   `mk_fenv_go` pre-sizes the table, so an index build no longer rehashes
//!   its way up through `log n` capacities.
//! * `dup` is still `O(|env|)`, so the *superlinear* item is smaller, not
//!   gone.  Removing it needs the install routes to stop asking for a second
//!   *owned* view — an overlay that borrows the installed index and hands the
//!   block's constants back as a delta, folded into the owner at `O(block)` —
//!   which is a change to those routes' shape, not to this file.  DESIGN.md's
//!   task #34 records the measurement and the design.
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
use crate::ron::ptr::P;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/FEnv.lean:44-49 FEnv
/// The spec environment together with a name index whose lookup function
/// agrees with `Env.find?`.  Deviations: `Std.HashMap` is `crate::ron::hashmap`
/// (§3.3); the two `Nat`s — the per-entry installation counter and
/// `visibleBelow` — are `u64` (§3.3); and the stored record is *shared* with
/// `env.consts` rather than copied into the index (`P<ConstantInfo>`, the
/// `env::Env` deviation: the Lean's one record, reached from two places).
pub struct FEnv {
    pub env: Env,
    pub idx: HashMap<Name, (u64, P<ConstantInfo>)>,
    /// Entries with counter `< visible_below` are visible; also the next
    /// counter `push` hands out.
    pub visible_below: u64,
}

/// con-leche: ConLeche/Kernel/FEnv.lean:56-60 mkFEnvGo
/// The index build, from the back of the cited list: the newest constant is
/// inserted last and wins, exactly as `List.find?` takes the first match — so
/// the agreement with `Env.find?` is unconditional (no freshness assumption).
/// The `u64` component is the running counter, so the build stays linear (the
/// tail's length is returned, not recomputed).
///
/// Deviations: the cited `List` recursion is the index recursion of task #3,
/// and since `env.consts` is stored oldest-first (`env::Env`'s deviation) "the
/// back of the cited list" is the **front** of this `Vec`: `mk_fenv_go(cs, i,
/// c, m)` inserts `cs[i..]` into `m` in *increasing* `i`, each entry with its
/// own index as its counter, so the table and the counter are threaded down
/// rather than built up and the recursion is a tail call.  The empty `∅` is
/// `HashMap::with_capacity(cs.len())` at the entry point rather than
/// `HashMap::new()` — the same empty table (task #7 documented the capacity as
/// invisible to the abstract map), sized for the inserts that follow, so a
/// build no longer rehashes its way up through `log n` capacities
/// (`move_elements_from_list` was 0.54 % of `Init` before task #34).  And the
/// record is shared, not copied.
pub fn mk_fenv_go(
    cs: &Vec<P<ConstantInfo>>,
    i: usize,
    c: u64,
    m: HashMap<Name, (u64, P<ConstantInfo>)>,
) -> (u64, HashMap<Name, (u64, P<ConstantInfo>)>) {
    if i >= cs.len() {
        (c, m)
    } else {
        let mut m = m;
        m.insert(
            env::constant_info_name(&cs[i]),
            (c, env::constant_info_rc_dup(&cs[i])),
        );
        mk_fenv_go(cs, i + 1, c + 1, m)
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:64-66 mkFEnv
/// Build the index of `env`, with nothing hidden (`visibleBelow` is the
/// constant count).  Takes the environment by value: the `FEnv` owns it.
pub fn mk_fenv(env: Env) -> FEnv {
    let p = mk_fenv_go(
        &env.consts,
        0,
        0,
        HashMap::with_capacity(env.consts.len()),
    );
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
/// and `ci :: fe.env.consts` is `Vec::push(ci)` — `Env.consts` is the cited
/// list *reversed* (`env::Env`'s deviation, task #50), so the cons is a push
/// at the back: `O(1)` amortised, as Lean's is, and **not** `Vec::insert`,
/// whose Aeneas model is an overwrite (`AENEAS_FINDINGS.md` §3.9).  The
/// constant is stored **once** and reached from both the list and the index,
/// as Lean's runtime stores it (`env::constant_info_share`); before task #34
/// the index held a `constant_info_dup` of it.
pub fn push(fe: FEnv, ci: ConstantInfo) -> FEnv {
    let mut consts = fe.env.consts;
    let mut idx = fe.idx;
    let rc: P<ConstantInfo> = env::constant_info_share(ci);
    idx.insert(
        env::constant_info_name(&rc),
        (fe.visible_below, env::constant_info_rc_dup(&rc)),
    );
    consts.push(rc);
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
/// con-leche: ConLeche/Kernel/Core.lean:1037-1042 towerSlotsAll
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
/// con-leche: ConLeche/Kernel/Core.lean:1044-1052 recSlotsAll
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
/// view.  Since task #34 neither half of the copy touches a record: the list
/// copy is `n` `P` bumps and the rebuild inserts those same handles into a
/// pre-sized table (the module note has the measurement that kept the index a
/// flat owned map instead of a shared one).
pub fn dup(fe: &FEnv) -> FEnv {
    let p = mk_fenv_go(
        &fe.env.consts,
        0,
        0,
        HashMap::with_capacity(fe.env.consts.len()),
    );
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
        let e = env::env_of(&vec![ax("c"), ax("b"), ax("a")]);
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
        // `consts` is the cited list reversed: oldest first, newest last
        // (`env::Env`'s deviation, task #50)
        assert!(name::beq(
            &env::constant_info_name(&fe.env.consts[0]),
            &nm("a")
        ));
        assert!(name::beq(
            &env::constant_info_name(&fe.env.consts[2]),
            &nm("c")
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
