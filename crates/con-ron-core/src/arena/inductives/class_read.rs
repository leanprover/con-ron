//! `arena::inductives::class_read` — the generated recursor stage's PRE-PASS
//! (UNVERIFIED in con-leche's sense: soundness never depends on it).
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/ClassRead.lean`, which is
//! `ConLeche/Kernel/Inductives/ClassRead.lean` over handles: read the classes
//! (one per motive), the prefix layout (motives, minor premises and their
//! inductive hypotheses) and every recursor's class off the stream's raw
//! recursor types, syntactically, checking nothing.
//!
//! ## The twin's deviations
//!
//! * **`classRead`'s `nPc : Name → Nat` is specialised** to its one
//!   instantiation, `classNPcOf p fe₁` (`arena::inductives::gen_rec`): the
//!   port takes the block's shape and the formers' environment.
//! * **`openPisAtFvars` is `open_pis_at_fvars_f`**, the one-pass form
//!   con-leche swaps in by `@[csimp]`.
//! * **A pure reading computed twice is computed once**
//!   (`classReadMinor`'s `fvarTypeD.piResult` per field).

use super::block_parts::{BlockShape, RecShape};
use super::field_tele::pi_binders;
use super::gen_rec::class_n_pc_of;
use crate::arena::checker_base;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::IFEnv;
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LsIdx, NIdx, ETAG_CONST, ETAG_FORALL_E, ETAG_FVAR, ETAG_SORT};
use crate::arena::monad::{fail_dangling_e, intern_e_fvar, view_bind, view_const, view_fvar_idx, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types::CheckError;
use crate::kernel::expr_ops::sub_nat;
use crate::ron::hashmap::Dup;

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:37-43 ClassKey
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean ClassKey` — a class: an
/// inductive at the levels `lvls` (interned) and the parameters `ds`.
pub struct ClassKey {
    pub ind: NIdx,
    pub lvls: LsIdx,
    pub ds: Vec<EIdx>,
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:37-43 ClassKey
/// The record copy.
pub fn class_key_dup(k: &ClassKey) -> ClassKey {
    ClassKey {
        ind: k.ind.dup2(),
        lvls: k.lvls.dup2(),
        ds: env::eidx_vec_dup(&k.ds),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:45-53 ClassSlot
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean ClassSlot` — one
/// binder of the recursors' shared prefix after the parameters: a motive
/// (its class), or a minor premise (the class ordinal it concludes at, the
/// constructor it builds, its inductive hypotheses `(field, class)`).
pub enum ClassSlot {
    Motive(ClassKey),
    Minor(u64, NIdx, Vec<(u64, u64)>),
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:45-53 ClassSlot
/// The copy.
pub fn class_slot_dup(s: &ClassSlot) -> ClassSlot {
    match s {
        ClassSlot::Motive(k) => ClassSlot::Motive(class_key_dup(k)),
        ClassSlot::Minor(c, n, ihs) => ClassSlot::Minor(*c, n.dup2(), pairs_dup(ihs, 0, Vec::new())),
    }
}

/// con-leche: none — a `List (Nat × Nat)` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean ClassSlot`.
pub fn pairs_dup(xs: &Vec<(u64, u64)>, i: usize, out: Vec<(u64, u64)>) -> Vec<(u64, u64)> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<(u64, u64)> = out;
        o.push((xs[i].0, xs[i].1));
        pairs_dup(xs, i + 1, o)
    }
}

/// con-leche: none — a `List ClassSlot` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean ClassSlot`.
pub fn slots_dup(xs: &Vec<ClassSlot>, i: usize, out: Vec<ClassSlot>) -> Vec<ClassSlot> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<ClassSlot> = out;
        o.push(class_slot_dup(&xs[i]));
        slots_dup(xs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:55-61 ClassRead
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean ClassRead` — what the
/// pre-pass read: the prefix after the parameters, and per recursor the class
/// its conclusion eliminates.
pub struct ClassRead {
    pub slots: Vec<ClassSlot>,
    pub rec_cls: Vec<u64>,
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:65-67 ClassRead.classes
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean ClassRead.classes` — the
/// classes (the motives' keys), in prefix order.
pub fn classes(slots: &Vec<ClassSlot>, i: usize, out: Vec<ClassKey>) -> Vec<ClassKey> {
    if i >= slots.len() {
        out
    } else {
        match &slots[i] {
            ClassSlot::Motive(k) => {
                let mut o: Vec<ClassKey> = out;
                o.push(class_key_dup(k));
                classes(slots, i + 1, o)
            }
            ClassSlot::Minor(_, _, _) => classes(slots, i + 1, out),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:65-67 ClassRead.classes
/// Lean twin: the `.motive _` test of a slot.
pub fn is_motive(s: &ClassSlot) -> bool {
    match s {
        ClassSlot::Motive(_) => true,
        ClassSlot::Minor(_, _, _) => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:69-73 ClassRead.motiveSlot
/// Lean twin: `(List.range slots.length).filter (motive at ·)` — the prefix
/// positions of the motives, in order.
pub fn motive_positions(slots: &Vec<ClassSlot>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= slots.len() {
        out
    } else if is_motive(&slots[i]) {
        let mut o: Vec<u64> = out;
        o.push(i as u64);
        motive_positions(slots, i + 1, o)
    } else {
        motive_positions(slots, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:69-73 ClassRead.motiveSlot
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean ClassRead.motiveSlot` —
/// the prefix position (after the parameters) of class `c`'s motive.
pub fn motive_slot(slots: &Vec<ClassSlot>, c: u64) -> Option<u64> {
    let ms: Vec<u64> = motive_positions(slots, 0, Vec::new());
    if c < ms.len() as u64 {
        Some(ms[c as usize])
    } else {
        None
    }
}

/// con-leche: none — `List.findIdx? (· == x)` on a `Nat` list
/// Lean twin: `motPos.findIdx? (· == x)`.
pub fn u64_find_idx(xs: &Vec<u64>, x: u64, i: usize) -> Option<u64> {
    if i >= xs.len() {
        None
    } else if xs[i] == x {
        Some(i as u64)
    } else {
        u64_find_idx(xs, x, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:77-80 classOfMotiveVar
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean classOfMotiveVar` — the
/// motive ordinal of the prefix variable `fvar p` (`nP ≤ p`), when that binder
/// is a motive.
pub fn class_of_motive_var(n_p: u64, mot_pos: &Vec<u64>, p: u64) -> Option<u64> {
    if n_p <= p {
        u64_find_idx(mot_pos, p - n_p, 0)
    } else {
        None
    }
}

/// con-leche: none — `xs.getLast?` on a handle list
/// Lean twin: `List.getLast?`.
pub fn eidx_last(xs: &Vec<EIdx>) -> Option<EIdx> {
    if xs.len() == 0 {
        None
    } else {
        Some(xs[xs.len() - 1].dup2())
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean classReadMinor` — the
/// `fvar` head of an application, its index (`none` at any other head).
pub fn fvar_head(pers: &PersTier, st: &AState, e: &EIdx) -> Result<Option<u64>, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(hd) => {
            if hd.tag() == ETAG_FVAR {
                match view_fvar_idx(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some(p) => Ok(Some(p)),
                }
            } else {
                Ok(None)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean classReadMinor` — one
/// opened binder `q` of a minor premise read as an inductive hypothesis: its
/// type's conclusion is a motive applied to a field `f` of the minor (`d ≤
/// f`), giving `(f - d, t)`.
pub fn class_read_ih(
    pers: &PersTier,
    st: &AState,
    n_p: u64,
    mot_pos: &Vec<u64>,
    d: u64,
    x: &EIdx,
) -> Result<Option<(u64, u64)>, CheckError> {
    match expr_ops::fvar_type_d(pers, st, x) {
        Err(e) => Err(e),
        Ok(ty) => match expr_ops::pi_result(pers, st, CORE_WALK_FUEL, &ty) {
            Err(e) => Err(e),
            Ok(r) => match fvar_head(pers, st, &r) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(p2)) => match class_of_motive_var(n_p, mot_pos, p2) {
                    None => Ok(None),
                    Some(t) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &r) {
                        Err(e) => Err(e),
                        Ok(args) => match eidx_last(&args) {
                            None => Ok(None),
                            Some(a) => match fvar_head(pers, st, &a) {
                                Err(e) => Err(e),
                                Ok(None) => Ok(None),
                                Ok(Some(f)) => {
                                    if d <= f {
                                        Ok(Some((f - d, t)))
                                    } else {
                                        Ok(None)
                                    }
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor
/// Lean twin: `(List.range fvs.length).filterMap …` — the inductive hypotheses
/// among the opened binders from `q` on, in order.
#[allow(clippy::too_many_arguments)]
pub fn class_read_ihs(
    pers: &PersTier,
    st: &AState,
    n_p: u64,
    mot_pos: &Vec<u64>,
    d: u64,
    fvs: &Vec<EIdx>,
    q: usize,
    out: Vec<(u64, u64)>,
) -> Result<Vec<(u64, u64)>, CheckError> {
    if q >= fvs.len() {
        Ok(out)
    } else {
        match class_read_ih(pers, st, n_p, mot_pos, d, &fvs[q]) {
            Err(e) => Err(e),
            Ok(Some(x)) => {
                let mut o: Vec<(u64, u64)> = out;
                o.push(x);
                class_read_ihs(pers, st, n_p, mot_pos, d, fvs, q + 1, o)
            }
            Ok(None) => class_read_ihs(pers, st, n_p, mot_pos, d, fvs, q + 1, out),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean classReadMinor` —
/// **read one minor premise's type `dom`**, opened at depth `d`: its
/// conclusion is a motive (the class), its last argument a constructor
/// application (the constructor), and its inductive hypotheses.
pub fn class_read_minor(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    mot_pos: &Vec<u64>,
    d: u64,
    dom: &EIdx,
) -> Result<Option<ClassSlot>, CheckError> {
    match pi_binders(pers, st, CORE_WALK_FUEL, dom, Vec::new()) {
        Err(e) => Err(e),
        Ok((bs, _)) => match checker_base::open_pis_at_fvars_f(pers, st, bs.len() as u64, dom, d) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((fvs, concl))) => match fvar_head(pers, st, &concl) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(p)) => match class_of_motive_var(n_p, mot_pos, p) {
                    None => Ok(None),
                    Some(c) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &concl) {
                        Err(e) => Err(e),
                        Ok(args) => match eidx_last(&args) {
                            None => Ok(None),
                            Some(last) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &last) {
                                Err(e) => Err(e),
                                Ok(hd) => {
                                    if hd.tag() == ETAG_CONST {
                                        match view_const(pers, st, &hd) {
                                            None => fail_dangling_e(),
                                            Some((cn, _)) => match class_read_ihs(pers, st, n_p, mot_pos, d, &fvs, 0, Vec::new()) {
                                                Err(e) => Err(e),
                                                Ok(ihs) => Ok(Some(ClassSlot::Minor(c, cn, ihs))),
                                            },
                                        }
                                    } else {
                                        Ok(None)
                                    }
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:107-124 classReadSlots
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean classReadSlots` — one
/// prefix binder's domain read as a motive (its telescope ends in a sort:
/// the class is its last binder's domain, at the class's parameter count)
/// or as a minor premise.
#[allow(clippy::too_many_arguments)]
pub fn class_read_slot(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    fe: &IFEnv,
    np: u64,
    mot_pos: &Vec<u64>,
    d: u64,
    dom: &EIdx,
) -> Result<Option<ClassSlot>, CheckError> {
    match expr_ops::pi_result(pers, st, CORE_WALK_FUEL, dom) {
        Err(e) => Err(e),
        Ok(r) => {
            if r.tag() == ETAG_SORT {
                match pi_binders(pers, st, CORE_WALK_FUEL, dom, Vec::new()) {
                    Err(e) => Err(e),
                    Ok((bs, _)) => {
                        if bs.len() == 0 {
                            Ok(None)
                        } else {
                            let mdom: EIdx = bs[bs.len() - 1].0.dup2();
                            match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &mdom) {
                                Err(e) => Err(e),
                                Ok(hd) => {
                                    if hd.tag() == ETAG_CONST {
                                        match view_const(pers, st, &hd) {
                                            None => fail_dangling_e(),
                                            Some((i_name, us)) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &mdom) {
                                                Err(e) => Err(e),
                                                Ok(args) => {
                                                    let n: u64 = class_n_pc_of(p, fe, &i_name);
                                                    Ok(Some(ClassSlot::Motive(ClassKey {
                                                        ind: i_name,
                                                        lvls: us,
                                                        ds: expr_ops::take_eidx_n(&args, n),
                                                    })))
                                                }
                                            },
                                        }
                                    } else {
                                        Ok(None)
                                    }
                                }
                            }
                        }
                    }
                }
            } else {
                class_read_minor(pers, st, np, mot_pos, d, dom)
            }
        }
    }
}

/// con-leche: none — `xs ++ [x]` on a `Nat` list
/// Lean twin: `motPos ++ [d - np]`.
pub fn u64_snoc(xs: &Vec<u64>, x: u64) -> Vec<u64> {
    let mut o: Vec<u64> = crate::arena::inductives::positivity::u64_vec_dup(xs, 0, Vec::new());
    o.push(x);
    o
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:107-124 classReadSlots
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean classReadSlots` — read
/// the prefix binders `n` of a recursor type opened at the parameters (`e`,
/// depth `d`), classifying each as a motive or a minor premise; each binder
/// opened at `d` before the next is read.  `none` off the shape.
#[allow(clippy::too_many_arguments)]
pub fn class_read_slots(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    fe: &IFEnv,
    np: u64,
    n: u64,
    mot_pos: &Vec<u64>,
    d: u64,
    e: &EIdx,
    out: Vec<ClassSlot>,
) -> Result<Option<Vec<ClassSlot>>, CheckError> {
    if n == 0 {
        Ok(Some(out))
    } else if e.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, e) {
            None => fail_dangling_e(),
            Some((dom, body, _)) => match class_read_slot(pers, st, p, fe, np, mot_pos, d, &dom) {
                Err(er) => Err(er),
                Ok(None) => Ok(None),
                Ok(Some(slot)) => {
                    let mot_pos2: Vec<u64> = if is_motive(&slot) {
                        u64_snoc(mot_pos, sub_nat(d, np))
                    } else {
                        crate::arena::inductives::positivity::u64_vec_dup(mot_pos, 0, Vec::new())
                    };
                    match intern_e_fvar(pers, st, d, dom) {
                        Err(er) => Err(er),
                        Ok(fv) => match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                            Err(er) => Err(er),
                            Ok(b2) => {
                                let mut o: Vec<ClassSlot> = out;
                                o.push(slot);
                                class_read_slots(pers, st, p, fe, np, n - 1, &mot_pos2, d + 1, &b2, o)
                            }
                        },
                    }
                }
            },
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:126-140 classRead
/// Lean twin: `recs.mapM fun rc => …` — every recursor's class off its
/// conclusion `motive_c ı⃗ t`, from `i` on; `none` off the shape.
#[allow(clippy::too_many_arguments)]
pub fn class_read_rec_cls(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    mot_pos: &Vec<u64>,
    recs: &Vec<RecShape>,
    i: usize,
    out: Vec<u64>,
) -> Result<Option<Vec<u64>>, CheckError> {
    if i >= recs.len() {
        Ok(Some(out))
    } else {
        let ty: EIdx = recs[i].cv_r.ty.dup2();
        match checker_base::open_pis_at_fvars_f(pers, st, recs[i].m_i + 1, &ty, 0) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((_, concl))) => match fvar_head(pers, st, &concl) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(p)) => match class_of_motive_var(n_p, mot_pos, p) {
                    None => Ok(None),
                    Some(c) => {
                        let mut o: Vec<u64> = out;
                        o.push(c);
                        class_read_rec_cls(pers, st, n_p, mot_pos, recs, i + 1, o)
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:126-140 classRead
/// Lean twin: `proof/ConRon/Arena/Inductives/ClassRead.lean classRead` — **the
/// pre-pass**: the prefix layout off the FIRST recursor's type, and every
/// recursor's class off its conclusion.  `none` when the family is not of the
/// generated shape.  `nPc` is `classNPcOf p fe` (the module note).
pub fn class_read(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    fe: &IFEnv,
    n_p: u64,
    recs: &Vec<RecShape>,
) -> Result<Option<ClassRead>, CheckError> {
    if recs.len() == 0 {
        Ok(None)
    } else {
        let ty: EIdx = recs[0].cv_r.ty.dup2();
        let r_p: u64 = recs[0].r_p;
        match checker_base::open_pis_at_fvars_f(pers, st, n_p, &ty, 0) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((_, body))) => {
                let empty: Vec<u64> = Vec::new();
                match class_read_slots(pers, st, p, fe, n_p, sub_nat(r_p, n_p), &empty, n_p, &body, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(slots)) => {
                        let mot_pos: Vec<u64> = motive_positions(&slots, 0, Vec::new());
                        match class_read_rec_cls(pers, st, n_p, &mot_pos, recs, 0, Vec::new()) {
                            Err(e) => Err(e),
                            Ok(None) => Ok(None),
                            Ok(Some(rec_cls)) => Ok(Some(ClassRead { slots, rec_cls })),
                        }
                    }
                }
            }
        }
    }
}
