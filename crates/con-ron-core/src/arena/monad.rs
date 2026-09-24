//! `arena::monad` — the monad, the state and the store primitives of (C).
//!
//! The Rust twin of `proof/ConRon/Arena/Monad.lean`, function for function,
//! under DESIGN.md §8.6's lockstep ruling (the Lean twin and the Rust are
//! written together, proofs later).  It is the seam between task #97-P4a's
//! frozen store layer (`arena::{handle, store}`) and every twin above it.
//!
//! ## `AM` is `&PersTier` plus `&mut AState` plus `Result`
//!
//! The twin's monad is `AM := ReaderT PersTier (StateT AState (Except
//! CheckError))` (DESIGN.md §8.4, amended by task #97-P6-6b).  Aeneas threads
//! a `&mut` parameter back as a returned value, passes a shared one straight
//! through and models `Result` as con-leche's `Except`
//! (`kernel::core_types`' note), so the Rust of `AM α` is
//!
//! | Lean | Rust |
//! |---|---|
//! | `AM α` | `fn(pers: &PersTier, st: &mut AState, …) -> Result<A, CheckError>` |
//! | `read` | `pers` |
//! | `pure a` | `Ok(a)` |
//! | `fail e` | `fail(e)`, i.e. `Err(e)` |
//! | `x ← m; k x` | `match m { Ok(x) => k(x), Err(e) => Err(e) }` |
//!
//! Two shapes of the twin come out narrower here, and both are deliberate:
//!
//! * **the reader is first and the state second, and neither is last.**  `AM`
//!   threads both invisibly, so putting `pers` and then `st` at the front
//!   leaves every other argument in the twin's own order, and `st` is the
//!   position `EStore`'s `&mut self` already occupies one layer down.  A
//!   function that cannot read the persistent tier on any path does not take
//!   `pers` at all — the twenty-two memo probes below are the largest such
//!   family — which costs the refinement nothing: `ReaderT` is free to
//!   ignore its environment.
//! * **a twin that cannot fail returns its value.**  `derivedE`, `derivedL`,
//!   `LIdx.hasParam` and the twenty-two memo probes are `AM α` only because
//!   `AM` is the module's one monad; none of them has a `fail` on any path.
//!   Their Rust reads the state and returns `α`.  Everything that *can*
//!   decline — a dangling handle, a full constructor array, exhausted fuel —
//!   returns `Result<α, CheckError>`, which is the twin's `Except` exactly.
//!
//! ## `CheckError` is `con-ron-core`'s
//!
//! `Monad.lean` declares its own four-constructor `CheckError` because the
//! Lean twin has no con-leche `Core.lean` in scope that carries the fourth
//! (`native`).  `con-ron-core`'s `kernel::core_types::CheckError` is already
//! that type — `NotImplemented`/`Invalid`/`Internal`/`Native`, DESIGN.md
//! §3.4's own list, with `Vec<u32>` payloads — so the port imports it rather
//! than declaring a second copy.
//!
//! ## The readback is shipped code here, not test code
//!
//! `Denote.lean` has no Rust counterpart (task #97-P4a: it is the arena's own
//! verification).  But `readName`/`readLevel`/`readLevels` are *shipped*
//! functions of `Monad.lean` — DESIGN.md §8.3's lesson 4, "intern the
//! representation, not the algorithm": a level ALGORITHM runs on a transient
//! `Level` tree read out of the store — and the twin implements them by
//! calling `denoteN`/`denoteL`/`denoteLs` directly, because "the cheapest
//! readback that is also *provably* the denotation is the denotation".  So
//! the three name/level/level-list readbacks of `Denote.lean` live here, in
//! the shipped crate, fuel and all.  `denoteE` does not: nothing above this
//! module reads an expression back, and the one place that needs it — the
//! differential test of `arena::expr_ops` — keeps its own copy in `mod
//! tests`, as `arena::store` does.

use crate::arena::core_state::reset_map;
use crate::arena::core_state::Caches;
use crate::arena::handle::{BMIdx, EIdx, LIdx, LsIdx, NIdx};
use crate::arena::handle::ETAG_LAM;
use crate::arena::pins::Pins;
use crate::arena::store::{
    ENodeView, EStore, LDer, LNodeView, LStore, LsNodeView, LsStore, NNodeView, NStore,
};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::expr::Literal;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::ron::hashmap::{Dup, Eq2, Hashable};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"arena: dangling expression handle"`, as code points.
const M_DANGLING_E: [u32; 33] = [
    97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 101, 120, 112,
    114, 101, 115, 115, 105, 111, 110, 32, 104, 97, 110, 100, 108, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"arena: dangling name handle"`, as code points.
const M_DANGLING_N: [u32; 27] = [
    97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 110, 97, 109, 101,
    32, 104, 97, 110, 100, 108, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"arena: dangling level handle"`, as code points.
const M_DANGLING_L: [u32; 28] = [
    97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 108, 101, 118,
    101, 108, 32, 104, 97, 110, 100, 108, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"arena: dangling level-list handle"`, as code points.
const M_DANGLING_LS: [u32; 33] = [
    97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 108, 101, 118,
    101, 108, 45, 108, 105, 115, 116, 32, 104, 97, 110, 100, 108, 101,
];

// ---------------------------------------------------------------------------
// The memo key (`Monad.lean:77-101 Memos`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:60-62 Inst1MemoInv
/// Lean twin: `proof/ConRon/Arena/Monad.lean:60-108 Memos` — the `(EIdx × Nat)`
/// key the nine handle-valued memo tables use: the node and the traversal
/// cursor (DESIGN.md §8.3 "Caches", nanoda's trick — the substituted term is
/// not in the key because the table is dropped at every top-level entry).
///
/// A struct rather than a tuple, exactly as `con_ron_core::kernel::expr_ops`'s
/// `ExprNatKey` is: Lean's `Prod` carries derived `BEq`/`Hashable` instances
/// and the port writes the two dictionaries by hand (§3.4's `Eq2`, not
/// `core::cmp`).
pub struct EIdxNat {
    pub h: EIdx,
    pub d: u64,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Monad.lean:60-108 Memos
/// Build a memo key, copying the handle (a `u32` read).
pub fn eidx_nat_key(h: &EIdx, d: u64) -> EIdxNat {
    EIdxNat { h: h.dup2(), d: d }
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
/// Lean twin: `proof/ConRon/Arena/Monad.lean:60-108 Memos`.  The handle *is*
/// its own hash (DESIGN.md §8.3's identity hashing), mixed with the cursor.
impl Hashable for EIdxNat {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(self.h.hash64(), name::nat_hash(self.d))
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
/// Lean twin: `proof/ConRon/Arena/Monad.lean:60-108 Memos`.  Handle equality is
/// word equality (`denoteE` is injective, task #97a's `denoteE_inj`).
impl Eq2 for EIdxNat {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &EIdxNat) -> bool {
        if self.h.eq2(&other.h) {
            self.d == other.d
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for EIdxNat {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> EIdxNat {
        EIdxNat { h: self.h.dup2(), d: self.d }
    }
}

// ---------------------------------------------------------------------------
// The per-call memo tables (`Monad.lean:70-108`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:60-62 Inst1MemoInv
/// Lean twin: `proof/ConRon/Arena/Monad.lean:60-108 Memos` — the memo tables of
/// the `ExprOps` twins, in one record.
///
/// con-leche threads each memo as an explicit argument-and-result pair
/// (`instantiate1Go v memo e d : Expr × Std.HashMap …`), and
/// `con_ron_core::kernel::expr_ops` turns that into a `&mut HashMap`
/// parameter; the arena carries the eleven tables in the state instead, which
/// is what lets a `…Fast` entry clear one without its callers seeing it.
///
/// **Eleven tables, one per con-leche `…Go`**, because the walks NEST:
/// `instantiate1Lift`'s `bvar` arm runs `liftLooseBVars`, so a shared table
/// would answer one walk with the other's answers.  Three of con-leche's
/// walks have no cursor (`resetMetaGo`, `renameConstsGo`, `instLPGo` key on
/// the node alone); the arena keys them at cursor `0`, so that all nine
/// handle-valued tables have one shape.
pub struct Memos {
    /// `instantiate1` (`ExprOps.lean:80-116`).
    pub inst1_c: HashMap<EIdxNat, EIdx>,
    /// `instantiateList` (`ExprOps.lean:267-303`).
    pub inst_l_c: HashMap<EIdxNat, EIdx>,
    /// `liftLooseBVars` (`ExprOps.lean:430-466`).
    pub lift_c: HashMap<EIdxNat, EIdx>,
    /// `resetMeta` (`ExprOps.lean:579-615`), at cursor `0`.
    pub reset_c: HashMap<EIdxNat, EIdx>,
    /// `renameConsts` (`ExprOps.lean:999-1036`), at cursor `0`.
    pub rename_c: HashMap<EIdxNat, EIdx>,
    /// `abstract1` (`ExprOps.lean:1789-1833`).
    pub abs1_c: HashMap<EIdxNat, EIdx>,
    /// `lowerBVars` (`ExprOps.lean:2012-2049`).
    pub lower_c: HashMap<EIdxNat, EIdx>,
    /// `instantiate1Lift` (`ExprOps.lean:2222-2261`).
    pub inst1_l_c: HashMap<EIdxNat, EIdx>,
    /// `instantiateLevelParams` (`ExprOps.lean:2564-2603`), at cursor `0`.
    pub inst_lp_c: HashMap<EIdxNat, EIdx>,
    /// `bvarBound` (`ExprOps.lean:1368-1392`).
    pub bvar_b_c: HashMap<EIdx, u64>,
    /// `fvarRange` (`ExprOps.lean:1397-1422`).
    pub fvar_b_c: HashMap<EIdx, u64>,
    /// con-leche: none — arena infrastructure (task #97-P6-13)
    /// **The level substitution at a LEVEL handle**, for `instLPGo`'s `.sort`
    /// arm: `ks` and `us` are fixed for the whole `instLPFast` call, so the
    /// handle alone is the key — DESIGN.md §8.3's own idiom, "cleared at every
    /// top-level call, so the substitution vector is not in the key".  A hit
    /// is one `u32`, where a miss reads the level back, substitutes and
    /// re-interns.
    pub inst_lp_l_c: HashMap<LIdx, LIdx>,
    /// con-leche: none — arena infrastructure (task #97-P6-13)
    /// The same at a universe-argument LIST handle, for the `.const` arm.
    pub inst_lp_ls_c: HashMap<LsIdx, LsIdx>,
    /// con-leche: none — arena infrastructure (task #97-PERF-WALKMEMO)
    /// **The two guard walks' memos, kept for their ALLOCATION only.**
    /// `allLevelParamsDefinedGo` and `constsResolveFGo` thread their memo as
    /// an argument (the twin's `(Bool, memo)` result), starting from `∅` at
    /// every entry; the port parks the table here between calls so that the
    /// next call starts from a cleared table instead of a `HashMap::new()`
    /// that re-grows by doubling (task #97-PERF-FRESH §3 item 1).  The entry
    /// moves it out, resets it (`arena::core_state::take_walk_memo`, which is
    /// the twin's `∅`) and puts it back after the walk, so nothing ever reads
    /// a row a previous call left; the twin's `Memos` has no counterpart, and
    /// Theorem 2's `MemosRel` has no clause for either (only `MemosInv`'s
    /// `Inv`).  `all_level_params_defined`'s table.
    pub lp_def_c: HashMap<EIdx, bool>,
    /// con-leche: none — arena infrastructure (task #97-PERF-WALKMEMO)
    /// `consts_resolve_f_fast`'s table; see `lp_def_c`.
    pub crf_c: HashMap<EIdx, bool>,
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:110-113 Memos.empty` — every walk
/// starts from the empty memo (`(instantiate1Go v {} e d).1`), so this is what
/// a top-level entry installs.  `HashMap::new` allocates nothing (task #35),
/// so eleven empty tables cost eleven headers.
impl Memos {
    /// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
    /// Lean twin: `proof/ConRon/Arena/Monad.lean:110-113 Memos.empty`.
    pub fn empty() -> Memos {
        Memos {
            inst1_c: HashMap::new(),
            inst_l_c: HashMap::new(),
            lift_c: HashMap::new(),
            reset_c: HashMap::new(),
            rename_c: HashMap::new(),
            abs1_c: HashMap::new(),
            lower_c: HashMap::new(),
            inst1_l_c: HashMap::new(),
            inst_lp_c: HashMap::new(),
            bvar_b_c: HashMap::new(),
            fvar_b_c: HashMap::new(),
            inst_lp_l_c: HashMap::new(),
            inst_lp_ls_c: HashMap::new(),
            lp_def_c: HashMap::new(),
            crf_c: HashMap::new(),
        }
    }

    /// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
    /// Lean twin: `proof/ConRon/Arena/Monad.lean:110-113 Memos.empty` — the same
    /// value as `empty`, reached in place: `enter_scratch` runs this once per
    /// declaration, and `arena::core_state::reset_map`'s note is why the
    /// bucket arrays are kept rather than handed back (task #97-P6-1).
    ///
    /// **All THIRTEEN tables, and that is a fix** (task #97-P5-Bracket's
    /// finding 2).  `inst_lp_l_c` and `inst_lp_ls_c` — task #97-P6-16's two
    /// level-substitution memos at a `LIdx` and a `LsIdx` — were added after
    /// this body was written and were not added to it, so `reset` did not
    /// reach `empty` and the twin's `enterScratch` (`memos := Memos.empty`)
    /// and this did not agree.  The run never noticed, because
    /// `inst_lp_clear` clears all three at every entry to
    /// `instantiate_level_params_fast`; Theorem 2's `enter_scratch_refines`
    /// did, because `MemosRel _ Memos.empty` is false of a table that still
    /// holds a row.
    pub fn reset(&mut self) {
        reset_map(&mut self.inst1_c);
        reset_map(&mut self.inst_l_c);
        reset_map(&mut self.lift_c);
        reset_map(&mut self.reset_c);
        reset_map(&mut self.rename_c);
        reset_map(&mut self.abs1_c);
        reset_map(&mut self.lower_c);
        reset_map(&mut self.inst1_l_c);
        reset_map(&mut self.inst_lp_c);
        reset_map(&mut self.bvar_b_c);
        reset_map(&mut self.fvar_b_c);
        reset_map(&mut self.inst_lp_l_c);
        reset_map(&mut self.inst_lp_ls_c)
    }
}

// ---------------------------------------------------------------------------
// The state (`Monad.lean:110-126`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:127-156 CState
/// Lean twin: `proof/ConRon/Arena/Monad.lean:119-136 AState` — the checker
/// state of (C): the arena, the per-call memo tables and — since task
/// #97-P4c — the per-declaration caches (`whnfCore`, `whnf`, the three infer
/// grades, `defeq`, the level verdicts, the instantiated constants).
pub struct AState {
    pub store: EStore,
    pub memos: Memos,
    /// The per-DECLARATION caches (task #97-P4c, `arena::core_state`): the
    /// five entry-point memos, the `defeq` verdict table, the two
    /// level-verdict tables and the three lazy instantiated-constant tables.
    /// A record of its own beside `memos`, because the per-call clear and the
    /// per-declaration drop are different operations on different lifetimes.
    pub caches: Caches,
    /// The reserved-name pins (task #97-P6-4a, `arena::pins`): the
    /// forty-nine constant names, the empty level list, the level `0` and
    /// `Sort 1`, interned ONCE into the persistent tier by the driver's
    /// `intern_all_pins` and read by handle ever after.  Empty until then,
    /// which is what makes a premature read a stop rather than a wrong
    /// answer (task #97c's hazard).
    pub pins: Pins,
}

/// con-leche: none — the initial state over a given arena
/// Lean twin: `proof/ConRon/Arena/Monad.lean:145-146 AState.init`.
impl AState {
    /// con-leche: none — the initial state over a given arena
    /// Lean twin: `proof/ConRon/Arena/Monad.lean:145-146 AState.init`.
    pub fn init(st: EStore) -> AState {
        AState {
            store: st,
            memos: Memos::empty(),
            caches: Caches::empty(),
            pins: Pins::empty(),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:53-72 CheckError
/// Lean twin: `proof/ConRon/Arena/Monad.lean:148-153 fail` — **the one failure
/// primitive of (C)**, as it is of (B).
///
/// In the twin it exists because a bare `throw` in `StateT σ (Except ε)`
/// leaves `mvcgen` with universe metavariables and no spec applies (task
/// #97s's template rule 7); here it exists so that the two modules have the
/// same shape and so that a later `@[spec]`-style lemma about the Rust has
/// one function to talk about.  It is `Err`, spelled once.
pub fn fail<T>(e: CheckError) -> Result<T, CheckError> {
    Err(e)
}

// ---------------------------------------------------------------------------
// The expression store's primitives (`Monad.lean:130-166`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:157-164 view` — decode a handle.
/// A dangling handle is an internal error: the checker never builds one, and
/// the bridge claims nothing on failure.
#[inline(always)]
pub fn view(pers: &PersTier, st: &AState, h: &EIdx) -> Result<ENodeView, CheckError> {
    match st.store.view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_E))),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:157-164 view` — the `none` arm of
/// `view`, spelled once so that a caller of the projections below declines a
/// dangling handle with `view`'s own error and not a second one.
///
/// **`#[cold]` and `#[inline(never)]`, and they are worth 4.7 % of `Init`**
/// (task #97-P6-13).  This is the arm a *well-formed store never takes*
/// (`StoreWF` excludes a dangling handle), and after the tag-only constructor
/// test it is spelled at 135 more call sites than it was.  Inlined, each of
/// them carries `code_points`'s 33-word copy into the middle of a hot walk:
/// `core.rs`'s conversion alone went from −5.7 G to **+6.9 G** on `Init`
/// because the growth pushed `instantiate1_go` past LLVM's inlining threshold
/// (measured, four quarters of the file, each a win on its own).  With the
/// two attributes the same 135 sites are −2.30 % instructions and −1.3 %
/// cycles.  A codegen attribute: Charon does not read it and the extraction
/// is unchanged.
#[cold]
#[inline(never)]
pub fn fail_dangling_e<T>() -> Result<T, CheckError> {
    fail(CheckError::Internal(code_points(&M_DANGLING_E)))
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:336-338 viewApp` — `viewApp`, the
/// `app` PROJECTION of `view`. A walk that has already read the tag off the
/// handle word wants only the two children; going through `view` would cost the
/// store's ten-way tag jump table, a 32-byte `ENodeView` returned through an
/// sret slot, a second dispatch on the tag the caller already knows, and the
/// view's drop.
///
/// It returns `Option`, not `Result`, for the same reason the store's readers
/// do: a `Result<(EIdx, EIdx), CheckError>` is a 32-byte sret value, and
/// `Option<(EIdx, EIdx)>` comes back in registers.  The caller spells the
/// dangling-handle decline itself, with `view`'s own error.
#[inline(always)]
pub fn view_app(pers: &PersTier, st: &AState, h: &EIdx) -> Option<(EIdx, EIdx)> {
    st.store.view_app(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:340-342 viewBVar` — `viewBVar`,
/// the `bvar` projection.
#[inline(always)]
pub fn view_bvar(pers: &PersTier, st: &AState, h: &EIdx) -> Option<u64> {
    st.store.view_bvar(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:344-346 viewSort` — `viewSort`,
/// the `sort` projection.
#[inline(always)]
pub fn view_sort(pers: &PersTier, st: &AState, h: &EIdx) -> Option<LIdx> {
    st.store.view_sort(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:348-350 viewConst` — `viewConst`,
/// the `const` projection.
#[inline(always)]
pub fn view_const(pers: &PersTier, st: &AState, h: &EIdx) -> Option<(NIdx, LsIdx)> {
    st.store.view_const(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:352-355 viewConstName` —
/// `viewConstName`, the head NAME of a `const` node; the level arguments are
/// left in the store.
#[inline(always)]
pub fn view_const_name(pers: &PersTier, st: &AState, h: &EIdx) -> Option<NIdx> {
    st.store.view_const_name(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:357-359 viewFVarIdx` —
/// `viewFVarIdx`, the `fvar` index.
#[inline(always)]
pub fn view_fvar_idx(pers: &PersTier, st: &AState, h: &EIdx) -> Option<u64> {
    st.store.view_fvar_idx(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:361-364 viewFVarTy` —
/// `viewFVarTy`, the `fvar` binder type.
#[inline(always)]
pub fn view_fvar_ty(pers: &PersTier, st: &AState, h: &EIdx) -> Option<EIdx> {
    st.store.view_fvar_ty(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:366-368 viewLit` — `viewLit`, the
/// `lit` projection.
#[inline(always)]
pub fn view_lit(pers: &PersTier, st: &AState, h: &EIdx) -> Option<Literal> {
    st.store.view_lit(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:370-373 viewBind` — `viewBind`,
/// the binder projection.
#[inline(always)]
pub fn view_bind(pers: &PersTier, st: &AState, h: &EIdx) -> Option<(EIdx, EIdx, BinderMeta)> {
    st.store.view_bind(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
/// Lean twin: `proof/ConRon/Arena/Monad.lean:375-379 viewBindI` — `viewBindI`,
/// the binder projection that stops at the datum's HANDLE (see
/// `EStore::view_bind_i`).
#[inline(always)]
pub fn view_bind_i(pers: &PersTier, st: &AState, h: &EIdx) -> Option<(EIdx, EIdx, BMIdx)> {
    st.store.view_bind_i(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:386-389 viewLet` — `viewLet`, the
/// `letE` projection.
#[inline(always)]
pub fn view_let(pers: &PersTier, st: &AState, h: &EIdx) -> Option<(EIdx, EIdx, EIdx)> {
    st.store.view_let(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:391-394 viewProj` — `viewProj`,
/// the `proj` projection.
#[inline(always)]
pub fn view_proj(pers: &PersTier, st: &AState, h: &EIdx) -> Option<(NIdx, u64, EIdx)> {
    st.store.view_proj(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:166-171 derivedE` — the packed
/// derived word of a handle (the `data` computed field, lines 357-402), read
/// in `O(1)` off the derived column.  No path fails, so the Rust returns the
/// word rather than a `Result` (module note).
#[inline(always)]
pub fn derived_e(pers: &PersTier, st: &AState, h: &EIdx) -> u64 {
    st.store.derived(pers, h)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:276-307 internE`.
///
/// **The one place the two modules put the capacity test differently, and
/// they agree on the outcome.**  The twin's `EStore.intern` is total and
/// carries the `2^27` cap as `capOK`, a hypothesis of `intern_spec`, so the
/// twin tests `sizeOf v < Idx.idxCap` *here*, at the monadic wrapper, and
/// `throw`s `.native` (DESIGN.md §8.3: "the Rust raises `Native` at the
/// limit, the Lean `throw`s the same kind").  Task #97-P4a's Rust
/// `EStore::intern` already *is* that test — it returns
/// `Result<EIdx, CheckError>` with the same `Native` decline on the same
/// condition — so the wrapper is a delegation and the branch is one layer
/// down.  Same test, same error kind, same store.
pub fn intern_e(pers: &PersTier, st: &mut AState, v: ENodeView) -> Result<EIdx, CheckError> {
    st.store.intern(pers, v)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:403-404 internBVarE` — `internBVarE`,
/// the `bvar` arm of `proof/ConRon/Arena/Monad.lean:155-166 internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_bvar`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_bvar(
    pers: &PersTier,
    st: &mut AState,
    i: u64,
) -> Result<EIdx, CheckError> {
    st.store.intern_bvar(pers, i)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:403-406 internFVarE` — `internFVarE`,
/// the `fvar` arm of `proof/ConRon/Arena/Monad.lean:155-166 internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_fvar`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_fvar(
    pers: &PersTier,
    st: &mut AState,
    idx: u64,
    ty: EIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_fvar(pers, idx, ty)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:403-408 internSortE` — `internSortE`,
/// the `sort` arm of `proof/ConRon/Arena/Monad.lean:155-166 internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_sort`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_sort(
    pers: &PersTier,
    st: &mut AState,
    u: LIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_sort(pers, u)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:403-410 internConstE` —
/// `internConstE`, the `const` arm of `proof/ConRon/Arena/Monad.lean:155-166
/// internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_const`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_const(
    pers: &PersTier,
    st: &mut AState,
    n: NIdx,
    us: LsIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_const(pers, n, us)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:403-412 internAppE` — `internAppE`,
/// the `app` arm of `proof/ConRon/Arena/Monad.lean:155-166 internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_app`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_app(
    pers: &PersTier,
    st: &mut AState,
    f: EIdx,
    a: EIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_app(pers, f, a)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:403-415 internLamE` —
/// `internLamE`, the `lam` arm of `proof/ConRon/Arena/Monad.lean:155-166
/// internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_lam`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_lam(
    pers: &PersTier,
    st: &mut AState,
    ty: EIdx,
    body: EIdx,
    m: BinderMeta,
) -> Result<EIdx, CheckError> {
    st.store.intern_lam(pers, ty, body, m)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:196-226 internLamIE` —
/// `internLamIE`, the `lam` arm of `internE` at a binder datum the caller
/// already holds as a HANDLE.
#[inline(always)]
pub fn intern_e_lam_i(
    pers: &PersTier,
    st: &mut AState,
    ty: EIdx,
    body: EIdx,
    m: BMIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_lam_i(pers, ty, body, m)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:228-245 internForallEIE` —
/// `internForallEIE`, the `forall_e` arm of `internE` at a binder datum the
/// caller already holds as a HANDLE.
#[inline(always)]
pub fn intern_e_forall_e_i(
    pers: &PersTier,
    st: &mut AState,
    ty: EIdx,
    body: EIdx,
    m: BMIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_forall_e_i(pers, ty, body, m)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:427-431 internBindIE` —
/// `internBindIE`, the two binder arms at a tag the caller carries and a datum
/// it holds as a handle: the shape the rebuilding walks want, where
/// `e_bind_view` + `internE` stood.
#[inline(always)]
pub fn intern_e_bind_i(
    pers: &PersTier,
    st: &mut AState,
    tag: u32,
    ty: EIdx,
    body: EIdx,
    m: BMIdx,
) -> Result<EIdx, CheckError> {
    if tag == ETAG_LAM {
        st.store.intern_lam_i(pers, ty, body, m)
    } else {
        st.store.intern_forall_e_i(pers, ty, body, m)
    }
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:416-418 internForallEE` —
/// `internForallEE`, the `forall_e` arm of
/// `proof/ConRon/Arena/Monad.lean:155-166 internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_forall_e`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_forall_e(
    pers: &PersTier,
    st: &mut AState,
    ty: EIdx,
    body: EIdx,
    m: BinderMeta,
) -> Result<EIdx, CheckError> {
    st.store.intern_forall_e(pers, ty, body, m)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:419-420 internLetEE` — `internLetEE`,
/// the `let_e` arm of `proof/ConRon/Arena/Monad.lean:155-166 internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_let_e`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_let_e(
    pers: &PersTier,
    st: &mut AState,
    ty: EIdx,
    val: EIdx,
    body: EIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_let_e(pers, ty, val, body)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:419-422 internLitE` — `internLitE`,
/// the `lit` arm of `proof/ConRon/Arena/Monad.lean:155-166 internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_lit`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_lit(
    pers: &PersTier,
    st: &mut AState,
    l: Literal,
) -> Result<EIdx, CheckError> {
    st.store.intern_lit(pers, l)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:419-425 internProjE` —
/// `internProjE`, the `proj` arm of `proof/ConRon/Arena/Monad.lean:155-166
/// internE`.
///
/// `internE` takes an `ENodeView`, so every caller BUILT one — a 32-byte
/// value with a `BinderMeta` in it, passed by value, taken apart again by
/// `EStore::intern`'s dispatch and dropped.  This wrapper takes the arm's
/// fields and goes straight to `EStore::intern_proj`, so the view is never
/// built at all.  Same store operation, same decline; see `intern_e`'s note
/// for where the capacity test lives.
pub fn intern_e_proj(
    pers: &PersTier,
    st: &mut AState,
    n: NIdx,
    i: u64,
    e: EIdx,
) -> Result<EIdx, CheckError> {
    st.store.intern_proj(pers, n, i, e)
}

// ---------------------------------------------------------------------------
// The name store's primitives (`Monad.lean:168-222`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:435-440 viewN` — decode a name
/// handle.
pub fn view_n(pers: &PersTier, st: &AState, h: &NIdx) -> Result<NNodeView, CheckError> {
    match st.store.ns().view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_N))),
    }
}

/// con-leche: none — hash-cons a name node, through the nesting
/// Lean twin: `proof/ConRon/Arena/Monad.lean:442-458 internNNode` (the
/// capacity test is one layer down here; see `intern_e`).
pub fn intern_n_node(pers: &PersTier, st: &mut AState, v: NNodeView) -> Result<NIdx, CheckError> {
    st.store.intern_name(pers, v)
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Denote.lean:74-83 denoteNAux` — the
/// fuel-indexed readback of a name handle.  Shipped, not test-only: the level
/// readback below is a shipped function of `Monad.lean` and it needs this one
/// (module note).
pub fn denote_n_aux(pers: &PersTier, st: &NStore, fuel: u64, h: &NIdx) -> Option<Name> {
    if fuel == 0 {
        None
    } else {
        match st.view(pers, h) {
            None => None,
            Some(NNodeView::Anonymous) => Some(name::anonymous()),
            Some(NNodeView::Str(p, s)) => match denote_n_aux(pers, st, fuel - 1, &p) {
                Some(q) => Some(name::mk_str(q, s)),
                None => None,
            },
            Some(NNodeView::Num(p, n)) => match denote_n_aux(pers, st, fuel - 1, &p) {
                Some(q) => Some(name::mk_num(q, n)),
                None => None,
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Denote.lean:85-88 denoteN` — the readback of
/// a name handle, at the store's own node count as fuel.
pub fn denote_n(pers: &PersTier, st: &NStore, h: &NIdx) -> Option<Name> {
    denote_n_aux(pers, st, st.node_count(pers) as u64 + 1, h)
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:460-468 readName` — read a name
/// back out of the store as a transient `Name`.  Names are compared by handle
/// throughout the checker (DESIGN.md §8.3), so this is the error-text and
/// level-substitution path only, and the readback IS the denotation.
pub fn read_name(pers: &PersTier, st: &AState, h: &NIdx) -> Result<Name, CheckError> {
    match denote_n(pers, st.store.ns(), h) {
        Some(x) => Ok(x),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_N))),
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:470-479 readNames` — read a LIST
/// of name handles back.  The twin spells the `List` recursion as its own
/// helper because `ks.mapM readName` is a closure (DESIGN.md §3.4); the Rust
/// spells the same recursion over a `Vec` by a cursor, which is §3.4's own
/// rule and `-loops-to-rec`'s shape.
pub fn read_names(pers: &PersTier, st: &AState, ks: &Vec<NIdx>) -> Result<Vec<Name>, CheckError> {
    read_names_from(pers, st, ks, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:470-479 readNames` — the cursor
/// recursion behind `read_names`.
pub fn read_names_from(
    pers: &PersTier,
    st: &AState,
    ks: &Vec<NIdx>,
    i: usize,
    out: Vec<Name>,
) -> Result<Vec<Name>, CheckError> {
    if i >= ks.len() {
        Ok(out)
    } else {
        match read_name(pers, st, &ks[i]) {
            Ok(x) => {
                let mut out2 = out;
                out2.push(x);
                read_names_from(pers, st, ks, i + 1, out2)
            }
            Err(e) => Err(e),
        }
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:481-490 internName` — intern a
/// transient name.  Structural on `Name`, so no fuel: the tree is a value, not
/// a DAG.
pub fn intern_name(pers: &PersTier, st: &mut AState, n: &Name) -> Result<NIdx, CheckError> {
    match &n.0.kind {
        name::NameKind::Anonymous => intern_n_node(pers, st, NNodeView::Anonymous),
        name::NameKind::Str(p, s) => match intern_name(pers, st, p) {
            Ok(hp) => intern_n_node(pers, st, NNodeView::Str(hp, expr::str_copy(s))),
            Err(e) => Err(e),
        },
        name::NameKind::Num(p, k) => match intern_name(pers, st, p) {
            Ok(hp) => intern_n_node(pers, st, NNodeView::Num(hp, *k)),
            Err(e) => Err(e),
        },
    }
}

// ---------------------------------------------------------------------------
// The level store's primitives (`Monad.lean:224-287`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:494-500 viewL` — decode a level
/// handle.
pub fn view_l(pers: &PersTier, st: &AState, h: &LIdx) -> Result<LNodeView, CheckError> {
    match st.store.ls().view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_L))),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:502-507 derivedL` — the level's
/// derived pair (its 32-bit hash and its `hasParam` bit, the computed field at
/// lines 47-53), read in `O(1)`.  Total, so no `Result` (module note).
pub fn derived_l(pers: &PersTier, st: &AState, h: &LIdx) -> LDer {
    st.store.lder(pers, h)
}

/// con-leche: none — hash-cons a level node, through the nesting
/// Lean twin: `proof/ConRon/Arena/Monad.lean:509-525 internLNode` (the
/// capacity test is one layer down here; see `intern_e`).
pub fn intern_l_node(pers: &PersTier, st: &mut AState, v: LNodeView) -> Result<LIdx, CheckError> {
    st.store.intern_level(pers, v)
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Denote.lean:116-127 denoteLAux` — the
/// fuel-indexed readback of a level handle.
pub fn denote_l_aux(pers: &PersTier, st: &LStore, fuel: u64, h: &LIdx) -> Option<Level> {
    if fuel == 0 {
        None
    } else {
        match st.view(pers, h) {
            None => None,
            Some(LNodeView::Zero) => Some(level::zero()),
            Some(LNodeView::Succ(u)) => match denote_l_aux(pers, st, fuel - 1, &u) {
                Some(a) => Some(level::succ(a)),
                None => None,
            },
            Some(LNodeView::Max(u, v)) => match denote_l_aux(pers, st, fuel - 1, &u) {
                Some(a) => match denote_l_aux(pers, st, fuel - 1, &v) {
                    Some(b) => Some(level::max(a, b)),
                    None => None,
                },
                None => None,
            },
            Some(LNodeView::Imax(u, v)) => match denote_l_aux(pers, st, fuel - 1, &u) {
                Some(a) => match denote_l_aux(pers, st, fuel - 1, &v) {
                    Some(b) => Some(level::imax(a, b)),
                    None => None,
                },
                None => None,
            },
            Some(LNodeView::Param(n)) => match denote_n(pers, &st.ns, &n) {
                Some(q) => Some(level::param(q)),
                None => None,
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Denote.lean:129-132 denoteL` — the readback
/// of a level handle, at the store's own node count as fuel.
pub fn denote_l(pers: &PersTier, st: &LStore, h: &LIdx) -> Option<Level> {
    denote_l_aux(pers, st, st.node_count(pers) as u64 + 1, h)
}

/// con-leche: none — `denoteL` mapped over a level-handle list
/// Lean twin: `proof/ConRon/Arena/Denote.lean:168-171 denoteLList` — a list
/// node's children are level handles only, so there is no recursion through
/// `LsIdx` and no fuel.  The `List` recursion is a cursor over the `Vec`.
pub fn denote_l_list(pers: &PersTier, st: &LStore, us: &Vec<LIdx>) -> Option<Vec<Level>> {
    denote_l_list_from(pers, st, us, 0, Vec::new())
}

/// con-leche: none — `denoteL` mapped over a level-handle list
/// Lean twin: `proof/ConRon/Arena/Denote.lean:168-171 denoteLList` — the
/// cursor recursion behind `denote_l_list`.
pub fn denote_l_list_from(
    pers: &PersTier,
    st: &LStore,
    us: &Vec<LIdx>,
    i: usize,
    out: Vec<Level>,
) -> Option<Vec<Level>> {
    if i >= us.len() {
        Some(out)
    } else {
        match denote_l(pers, st, &us[i]) {
            None => None,
            Some(l) => {
                let mut out2 = out;
                out2.push(l);
                denote_l_list_from(pers, st, us, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — the readback of an interned universe-argument list
/// Lean twin: `proof/ConRon/Arena/Denote.lean:173-177 denoteLs`.
pub fn denote_ls(pers: &PersTier, st: &LsStore, h: &LsIdx) -> Option<Vec<Level>> {
    match st.view(pers, h) {
        None => None,
        Some(us) => denote_l_list(pers, &st.ls, &us),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:527-536 readLevel` — **the
/// readback** (DESIGN.md §8.3 lesson 4, "intern the representation, not the
/// algorithm"): a level ALGORITHM runs on a transient `Level` tree read out of
/// the store, never on handles.  The readback is `denote_l` itself, so the
/// later spec theorem for this primitive is an equation and not a simulation.
pub fn read_level(pers: &PersTier, st: &AState, h: &LIdx) -> Result<Level, CheckError> {
    match denote_l(pers, st.store.ls(), h) {
        Some(l) => Ok(l),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_L))),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:538-555 internLevel` — intern a
/// transient level tree.  Structural on `Level`, so no fuel.
pub fn intern_level(pers: &PersTier, st: &mut AState, l: &Level) -> Result<LIdx, CheckError> {
    match &l.0.kind {
        level::LevelKind::Zero => intern_l_node(pers, st, LNodeView::Zero),
        level::LevelKind::Succ(u) => match intern_level(pers, st, u) {
            Ok(hu) => intern_l_node(pers, st, LNodeView::Succ(hu)),
            Err(e) => Err(e),
        },
        level::LevelKind::Max(u, v) => match intern_level(pers, st, u) {
            Ok(hu) => match intern_level(pers, st, v) {
                Ok(hv) => intern_l_node(pers, st, LNodeView::Max(hu, hv)),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        },
        level::LevelKind::Imax(u, v) => match intern_level(pers, st, u) {
            Ok(hu) => match intern_level(pers, st, v) {
                Ok(hv) => intern_l_node(pers, st, LNodeView::Imax(hu, hv)),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        },
        level::LevelKind::Param(n) => match intern_name(pers, st, n) {
            Ok(hn) => intern_l_node(pers, st, LNodeView::Param(hn)),
            Err(e) => Err(e),
        },
    }
}

// ---------------------------------------------------------------------------
// The level-list store's primitives (`Monad.lean:289-330`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:559-565 viewLs` — the `none` arm
/// of `viewLs`, spelled once so that a caller of the length projection below
/// declines a dangling handle with `viewLs`'s own error and not a second one.
#[cold]
#[inline(never)]
pub fn fail_dangling_ls<T>() -> Result<T, CheckError> {
    fail(CheckError::Internal(code_points(&M_DANGLING_LS)))
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:607-612 viewLsLen` — `viewLsLen`,
/// the LENGTH projection of `viewLs`. Decoding a level-list handle copies its
/// whole `Vec<LIdx>` out of the node (Lean shares the list; DESIGN.md §3.2);
/// the callers that only compare the length with a declaration's
/// level-parameter count want this.
#[inline(always)]
pub fn view_ls_len(pers: &PersTier, st: &AState, h: &LsIdx) -> Option<usize> {
    st.store.ls_s().view_len(pers, h)
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:559-565 viewLs` — decode a
/// universe-argument list handle (the `const` node's second field, line 347).
pub fn view_ls(pers: &PersTier, st: &AState, h: &LsIdx) -> Result<LsNodeView, CheckError> {
    match st.store.ls_s().view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_LS))),
    }
}

/// con-leche: none — hash-cons a universe-argument list
/// Lean twin: `proof/ConRon/Arena/Monad.lean:567-583 internLsNode` (the
/// capacity test is one layer down here; see `intern_e`).
pub fn intern_ls_node(
    pers: &PersTier,
    st: &mut AState,
    v: LsNodeView,
) -> Result<LsIdx, CheckError>  {
    st.store.intern_levels(pers, v)
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:585-591 readLevels` — read a
/// universe argument list back as transient `Level` trees.
pub fn read_levels(pers: &PersTier, st: &AState, h: &LsIdx) -> Result<Vec<Level>, CheckError> {
    match denote_ls(pers, st.store.ls_s(), h) {
        Some(us) => Ok(us),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_LS))),
    }
}

/// con-leche: none — a value copy of a read-back universe-argument list
/// Lean twin: none — Lean's value semantics need no copy (DESIGN.md §3.2) — the
/// `Vec` copy Lean's value semantics hides (DESIGN.md §3.2): `Level` is a `P`
/// tree, so this is `n` reference bumps and one allocation.
pub fn level_list_dup(us: &Vec<Level>) -> Vec<Level> {
    level_list_dup_from(us, 0, Vec::new())
}

/// con-leche: none — the cursor recursion behind `level_list_dup`
/// Lean twin: none — Lean's value semantics need no copy (DESIGN.md §3.2).
pub fn level_list_dup_from(us: &Vec<Level>, i: usize, out: Vec<Level>) -> Vec<Level> {
    if i >= us.len() {
        out
    } else {
        let mut out2 = out;
        out2.push(level::dup(&us[i]));
        level_list_dup_from(us, i + 1, out2)
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// The readback memo's value copy, for `HashMap2::dup` of `Caches::read_l_c`
/// in `arena::checker_base::caches_dup` (task #97-T2-LOCKSTEP D4): a
/// reference bump.
impl Dup for Level {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> Level {
        level::dup(self)
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// The same for `Caches::read_n_c`'s values.
impl Dup for Name {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> Name {
        name::dup(self)
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// The same for `Caches::read_ls_c`'s values (`level_list_dup`).
impl Dup for Vec<Level> {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> Vec<Level> {
        level_list_dup(self)
    }
}

// ---------------------------------------------------------------------------
// The readback memo (task #97-P6-13; DESIGN.md §8.3's "memoised readback per
// declaration", which nothing had built)
// ---------------------------------------------------------------------------
//
// `readLevel`/`readNames`/`readLevels` rebuild a transient tree node by node
// out of the store every time they are asked, and the checker asks per
// OCCURRENCE: `instLPGo`'s `.sort` and `.const` arms, `Level.isEquiv`'s two
// misses, `proofPW`'s substitution and the recursor's comparands.  The
// denotation of a handle is a function of the handle and of the tier it names,
// so it is constant for exactly as long as the other ten cache tables are —
// `drop_scratch` flushes the caches and drops the tier in one operation
// (`core::drop_scratch`), which is what makes a stale row impossible.  A hit
// is a reference bump.

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:630-643 readLevelM` —
/// `readLevelM`, the memoised `readLevel`. Same value, same failure: a hit
/// answers with the row the miss stored, and `denoteL` is a function of the
/// store.
pub fn read_level_m(pers: &PersTier, st: &mut AState, h: &LIdx) -> Result<Level, CheckError> {
    match st.caches.read_l_c.get(h) {
        Some(l) => Ok(level::dup(l)),
        None => match denote_l(pers, st.store.ls(), h) {
            None => fail(CheckError::Internal(code_points(&M_DANGLING_L))),
            Some(l) => {
                st.caches.read_l_c.insert(h.dup2(), level::dup(&l));
                Ok(l)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:645-658 readNameM` — `readNameM`,
/// the memoised `readName`.
pub fn read_name_m(pers: &PersTier, st: &mut AState, h: &NIdx) -> Result<Name, CheckError> {
    match st.caches.read_n_c.get(h) {
        Some(x) => Ok(name::dup(x)),
        None => match denote_n(pers, st.store.ns(), h) {
            None => fail(CheckError::Internal(code_points(&M_DANGLING_N))),
            Some(x) => {
                st.caches.read_n_c.insert(h.dup2(), name::dup(&x));
                Ok(x)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:660-668 readNamesM` —
/// `readNamesM`, the memoised `readNames`.
pub fn read_names_m(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<NIdx>,
) -> Result<Vec<Name>, CheckError> {
    read_names_m_from(pers, st, ks, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:660-668 readNamesM` — the cursor
/// recursion behind `read_names_m`.
pub fn read_names_m_from(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<NIdx>,
    i: usize,
    out: Vec<Name>,
) -> Result<Vec<Name>, CheckError> {
    if i >= ks.len() {
        Ok(out)
    } else {
        match read_name_m(pers, st, &ks[i]) {
            Err(e) => Err(e),
            Ok(x) => {
                let mut out2 = out;
                out2.push(x);
                read_names_m_from(pers, st, ks, i + 1, out2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:670-683 readLevelsM` —
/// `readLevelsM`, the memoised `readLevels`.
pub fn read_levels_m(
    pers: &PersTier,
    st: &mut AState,
    h: &LsIdx,
) -> Result<Vec<Level>, CheckError> {
    match st.caches.read_ls_c.get(h) {
        Some(us) => Ok(level_list_dup(us)),
        None => match denote_ls(pers, st.store.ls_s(), h) {
            None => fail(CheckError::Internal(code_points(&M_DANGLING_LS))),
            Some(us) => {
                st.caches.read_ls_c.insert(h.dup2(), level_list_dup(&us));
                Ok(us)
            }
        },
    }
}

/// con-leche: none — intern a list of transient levels, one handle each
/// Lean twin: `proof/ConRon/Arena/Monad.lean:593-599 internLevelList`.
pub fn intern_level_list(
    pers: &PersTier,
    st: &mut AState,
    us: &Vec<Level>,
) -> Result<Vec<LIdx>, CheckError>  {
    intern_level_list_from(pers, st, us, 0, Vec::new())
}

/// con-leche: none — intern a list of transient levels, one handle each
/// Lean twin: `proof/ConRon/Arena/Monad.lean:593-599 internLevelList` — the
/// cursor recursion behind `intern_level_list`.
pub fn intern_level_list_from(
    pers: &PersTier,
    st: &mut AState,
    us: &Vec<Level>,
    i: usize,
    out: Vec<LIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    if i >= us.len() {
        Ok(out)
    } else {
        match intern_level(pers, st, &us[i]) {
            Ok(hu) => {
                let mut out2 = out;
                out2.push(hu);
                intern_level_list_from(pers, st, us, i + 1, out2)
            }
            Err(e) => Err(e),
        }
    }
}

/// con-leche: none — intern a list of transient levels and hash-cons the list node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:601-605 internLevels`.
pub fn intern_levels(
    pers: &PersTier,
    st: &mut AState,
    us: &Vec<Level>,
) -> Result<LsIdx, CheckError>  {
    match intern_level_list(pers, st, us) {
        Ok(hs) => intern_ls_node(pers, st, hs),
        Err(e) => Err(e),
    }
}

// ---------------------------------------------------------------------------
// Interning into the PERSISTENT tier — the promotion's primitives
// (`Monad.lean:329-397`, task #97-P6-2 — ADDITIVE)
// ---------------------------------------------------------------------------
//
// DESIGN.md §8.3, "Phase A runs in the scratch tier too, with promotion".
// Four twins of `intern_e` / `intern_n_node` / `intern_l_node` /
// `intern_ls_node` that append to the PERSISTENT tier while the store is in a
// declaration bracket — frozen, its persistent tables the `tier` the bracket
// owns (task #98-FREEZE) — over `arena::store`'s `PersTier::intern_*`.  The
// tier is written through `&mut`; the state is only read (the children's
// derived words).  The capacity test is the same one against the persistent
// array and the error is the same `Native` kind — and, as with `intern_e`,
// the test sits one layer down here (the twin's `internPersistentE` tests
// `sizeOf v < Idx.idxCap` at the wrapper; `PersTier::intern_e` already *is*
// that test).  `arena::promote` is the only caller.

/// con-leche: none — arena infrastructure; hash-cons an expression node into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:723-749 internPersistentE`.
pub fn intern_persistent_e(
    tier: &mut PersTier,
    st: &AState,
    v: ENodeView,
) -> Result<EIdx, CheckError> {
    tier.intern_e(&st.store, v)
}

/// con-leche: none — arena infrastructure; hash-cons a name node into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:751-765 internPersistentN`, through
/// the nesting.
pub fn intern_persistent_n(
    tier: &mut PersTier,
    st: &AState,
    v: NNodeView,
) -> Result<NIdx, CheckError> {
    tier.intern_n(&st.store.lss.ls.ns, v)
}

/// con-leche: none — arena infrastructure; hash-cons a level node into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:767-781 internPersistentL`, through
/// the nesting.
pub fn intern_persistent_l(
    tier: &mut PersTier,
    st: &AState,
    v: LNodeView,
) -> Result<LIdx, CheckError> {
    tier.intern_l(&st.store.lss.ls, v)
}

/// con-leche: none — arena infrastructure; hash-cons a universe-argument list into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:783-797 internPersistentLs`, through
/// the nesting.
pub fn intern_persistent_ls(
    tier: &mut PersTier,
    st: &AState,
    v: LsNodeView,
) -> Result<LsIdx, CheckError> {
    tier.intern_ls(&st.store.lss, v)
}

// ---------------------------------------------------------------------------
// The memo tables: one probe/record/drop triple per walk
// (`Monad.lean:334-479`)
//
// Nine handle-valued tables and two `u64`-valued ones.  The twin detaches each
// table before the update (DESIGN.md §8.4 lesson 14) and marks the mutators
// `@[noinline]` (lesson 15); neither has a Rust counterpart — `&mut` IS the
// unique reference the detaching exists to manufacture, and `@[noinline]` is a
// Lean reference-count concern (task #97-P4a's mapping table says the same of
// the store's mutations).  A drop is `HashMap::new()`, which is the twin's
// `:= ∅` term for term and allocates nothing (task #35).
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
/// Lean twin: `proof/ConRon/Arena/Monad.lean:806-809 inst1Get` — probe the
/// `instantiate1` memo.  The answer is owned, so the map's borrow ends with
/// the lookup and the miss branch can take the state mutably again
/// (`con_ron_core::kernel::expr_ops::memo1_get`'s reason).
pub fn inst1_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.inst1_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
/// Lean twin: `proof/ConRon/Arena/Monad.lean:811-817 inst1Set` — record an
/// `instantiate1` answer.
pub fn inst1_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst1_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:819-823 inst1Clear` — the memo is
/// "dropped after each call, since it also depends on `v`".
pub fn inst1_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst1_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:825-828 instLGet` — probe the
/// `instantiateList` memo.
pub fn inst_l_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.inst_l_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:830-836 instLSet` — record an
/// `instantiateList` answer.
pub fn inst_l_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst_l_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:838-842 instLClear` — drop the
/// `instantiateList` memo (it depends on `vs`).
pub fn inst_l_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst_l_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:844-847 liftGet` — probe the
/// `liftLooseBVars` memo.
pub fn lift_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.lift_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:849-855 liftSet` — record a
/// `liftLooseBVars` answer.
pub fn lift_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.lift_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:857-861 liftClear` — drop the
/// `liftLooseBVars` memo (it depends on `amount`).
pub fn lift_clear(st: &mut AState) {
    reset_map(&mut st.memos.lift_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:863-866 resetGet` — probe the
/// `resetMeta` memo.
pub fn reset_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.reset_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:868-874 resetSet` — record a
/// `resetMeta` answer.
pub fn reset_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.reset_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:876-880 resetClear` — drop the
/// `resetMeta` memo.
pub fn reset_clear(st: &mut AState) {
    reset_map(&mut st.memos.reset_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:882-885 renameGet` — probe the
/// `renameConsts` memo.
pub fn rename_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.rename_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:887-893 renameSet` — record a
/// `renameConsts` answer.
pub fn rename_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.rename_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1111-1113 renameConstsFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:895-899 renameClear` — drop the
/// `renameConsts` memo (it depends on the renaming).
pub fn rename_clear(st: &mut AState) {
    reset_map(&mut st.memos.rename_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go
/// Lean twin: `proof/ConRon/Arena/Monad.lean:901-904 abs1Get` — probe the
/// `abstract1` memo.
pub fn abs1_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.abs1_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go
/// Lean twin: `proof/ConRon/Arena/Monad.lean:906-912 abs1Set` — record an
/// `abstract1` answer.
pub fn abs1_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.abs1_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1929-1931 abstract1Fast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:914-918 abs1Clear` — drop the
/// `abstract1` memo (it depends on `d`).
pub fn abs1_clear(st: &mut AState) {
    reset_map(&mut st.memos.abs1_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:920-923 lowerGet` — probe the
/// `lowerBVars` memo.
pub fn lower_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.lower_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:925-931 lowerSet` — record a
/// `lowerBVars` answer.
pub fn lower_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.lower_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2146-2148 lowerBVarsFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:933-937 lowerClear` — drop the
/// `lowerBVars` memo (it depends on `amount`).
pub fn lower_clear(st: &mut AState) {
    reset_map(&mut st.memos.lower_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:939-942 inst1LGet` — probe the
/// `instantiate1Lift` memo.
pub fn inst1_l_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.inst1_l_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:944-950 inst1LSet` — record an
/// `instantiate1Lift` answer.
pub fn inst1_l_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst1_l_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2358-2360 instantiate1LiftFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:952-956 inst1LClear` — drop the
/// `instantiate1Lift` memo (it depends on `v`).
pub fn inst1_l_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst1_l_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:958-961 instLPGet` — probe the
/// level-substitution memo.
pub fn inst_lp_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.inst_lp_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:963-969 instLPSet` — record a
/// level-substitution answer.
pub fn inst_lp_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst_lp_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2720-2722 Expr.instLPFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:971-976 instLPClear` — drop the
/// level-substitution memo (it depends on `ks` and `us`).
pub fn inst_lp_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst_lp_c);
    reset_map(&mut st.memos.inst_lp_l_c);
    reset_map(&mut st.memos.inst_lp_ls_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:978-981 instLPLGet` — probe the
/// level-handle substitution memo.
pub fn inst_lp_l_get(st: &AState, h: &LIdx) -> Option<LIdx> {
    match st.memos.inst_lp_l_c.get(h) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:983-989 instLPLSet` — record a
/// level-handle substitution.
pub fn inst_lp_l_set(st: &mut AState, h: LIdx, r: &LIdx) {
    st.memos.inst_lp_l_c.insert(h, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:991-994 instLPLsGet` — probe the
/// level-LIST substitution memo.
pub fn inst_lp_ls_get(st: &AState, h: &LsIdx) -> Option<LsIdx> {
    match st.memos.inst_lp_ls_c.get(h) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:996-1002 instLPLsSet` — record a
/// level-LIST substitution.
pub fn inst_lp_ls_set(st: &mut AState, h: LsIdx, r: &LsIdx) {
    st.memos.inst_lp_ls_c.insert(h, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1370-1394 bvarBoundGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:1004-1007 bvarBGet` — probe the
/// loose-bvar-bound memo.
pub fn bvar_b_get(st: &AState, k: &EIdx) -> Option<u64> {
    match st.memos.bvar_b_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1370-1394 bvarBoundGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:1009-1015 bvarBSet` — record a
/// loose-bvar bound.
pub fn bvar_b_set(st: &mut AState, k: EIdx, r: u64) {
    st.memos.bvar_b_c.insert(k, r);
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1396-1397 bvarBoundMemo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:1017-1021 bvarBClear` — drop the
/// loose-bvar-bound memo.
pub fn bvar_b_clear(st: &mut AState) {
    reset_map(&mut st.memos.bvar_b_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1399-1424 fvarRangeGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:1023-1026 fvarBGet` — probe the
/// fvar-range memo.
pub fn fvar_b_get(st: &AState, k: &EIdx) -> Option<u64> {
    match st.memos.fvar_b_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1399-1424 fvarRangeGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:1028-1034 fvarBSet` — record an
/// fvar range.
pub fn fvar_b_set(st: &mut AState, k: EIdx, r: u64) {
    st.memos.fvar_b_c.insert(k, r);
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1426-1427 fvarRangeMemo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:1036-1040 fvarBClear` — drop the
/// fvar-range memo.
pub fn fvar_b_clear(st: &mut AState) {
    reset_map(&mut st.memos.fvar_b_c)
}
