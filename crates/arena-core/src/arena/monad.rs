//! `arena::monad` — the monad, the state and the store primitives of (C).
//!
//! The Rust twin of `proof/ConRon/Arena/Monad.lean`, function for function,
//! under DESIGN.md §8.6's lockstep ruling (the Lean twin and the Rust are
//! written together, proofs later).  It is the seam between task #97-P4a's
//! frozen store layer (`arena::{handle, store}`) and every twin above it.
//!
//! ## `AM` is `&mut AState` plus `Result`
//!
//! The twin's monad is `AM := StateT AState (Except CheckError)` and nothing
//! else (DESIGN.md §8.4).  Aeneas threads a `&mut` parameter back as a
//! returned value and models `Result` as con-leche's `Except`
//! (`kernel::core_types`' note), so the Rust of `AM α` is
//!
//! | Lean | Rust |
//! |---|---|
//! | `AM α` | `fn(st: &mut AState, …) -> Result<A, CheckError>` |
//! | `pure a` | `Ok(a)` |
//! | `fail e` | `fail(e)`, i.e. `Err(e)` |
//! | `x ← m; k x` | `match m { Ok(x) => k(x), Err(e) => Err(e) }` |
//!
//! Two shapes of the twin come out narrower here, and both are deliberate:
//!
//! * **the state parameter is first, not last.**  `AM` threads the state as
//!   an invisible first argument, so putting `st` first leaves every other
//!   argument in the twin's own order, and it is the position `EStore`'s
//!   `&mut self` already occupies one layer down.
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
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::pins::Pins;
use crate::arena::store::{
    ENodeView, EStore, LDer, LNodeView, LStore, LsNodeView, LsStore, NNodeView, NStore,
};
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use con_ron_core::ron::hashmap::{Dup, Eq2, Hashable};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use con_ron_core::ron::hashmap2::HashMap2 as HashMap;
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:77-101 Memos` — the `(EIdx × Nat)`
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Monad.lean:77-101 Memos
/// Build a memo key, copying the handle (a `u32` read).
pub fn eidx_nat_key(h: &EIdx, d: u64) -> EIdxNat {
    EIdxNat { h: h.dup2(), d: d }
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
/// Lean twin: `proof/ConRon/Arena/Monad.lean:77-101 Memos`.  The handle *is*
/// its own hash (DESIGN.md §8.3's identity hashing), mixed with the cursor.
impl Hashable for EIdxNat {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(self.h.hash64(), name::nat_hash(self.d))
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
/// Lean twin: `proof/ConRon/Arena/Monad.lean:77-101 Memos`.  Handle equality is
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:77-101 Memos` — the memo tables of
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
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:104 Memos.empty` — every walk
/// starts from the empty memo (`(instantiate1Go v {} e d).1`), so this is what
/// a top-level entry installs.  `HashMap::new` allocates nothing (task #35),
/// so eleven empty tables cost eleven headers.
impl Memos {
    /// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
    /// Lean twin: `proof/ConRon/Arena/Monad.lean:104 Memos.empty`.
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
        }
    }

    /// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
    /// Lean twin: `proof/ConRon/Arena/Monad.lean:104 Memos.empty` — the same
    /// value as `empty`, reached in place: `enter_scratch` runs this once per
    /// declaration, and `arena::core_state::reset_map`'s note is why the
    /// bucket arrays are kept rather than handed back (task #97-P6-1).
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
        reset_map(&mut self.fvar_b_c)
    }
}

// ---------------------------------------------------------------------------
// The state (`Monad.lean:110-126`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:127-156 CState
/// Lean twin: `proof/ConRon/Arena/Monad.lean:114-116 AState` — the checker
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:124 AState.init`.
impl AState {
    /// con-leche: none — the initial state over a given arena
    /// Lean twin: `proof/ConRon/Arena/Monad.lean:124 AState.init`.
    pub fn init(st: EStore) -> AState {
        AState {
            store: st,
            memos: Memos::empty(),
            caches: Caches::empty(),
            pins: Pins::empty(),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:47-66 CheckError
/// Lean twin: `proof/ConRon/Arena/Monad.lean:131 fail` — **the one failure
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

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:138-142 view` — decode a handle.
/// A dangling handle is an internal error: the checker never builds one, and
/// the bridge claims nothing on failure.
pub fn view(pers: &PersTier, st: &AState, h: &EIdx) -> Result<ENodeView, CheckError> {
    match st.store.view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_E))),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-402 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:147-149 derivedE` — the packed
/// derived word of a handle (the `data` computed field, lines 357-402), read
/// in `O(1)` off the derived column.  No path fails, so the Rust returns the
/// word rather than a `Result` (module note).
pub fn derived_e(pers: &PersTier, st: &AState, h: &EIdx) -> u64 {
    st.store.derived(pers, h)
}

/// con-leche: none — hash-cons an expression node
/// Lean twin: `proof/ConRon/Arena/Monad.lean:155-166 internE`.
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

// ---------------------------------------------------------------------------
// The name store's primitives (`Monad.lean:168-222`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:170-174 viewN` — decode a name
/// handle.
pub fn view_n(pers: &PersTier, st: &AState, h: &NIdx) -> Result<NNodeView, CheckError> {
    match st.store.ns().view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_N))),
    }
}

/// con-leche: none — hash-cons a name node, through the nesting
/// Lean twin: `proof/ConRon/Arena/Monad.lean:177-188 internNNode` (the
/// capacity test is one layer down here; see `intern_e`).
pub fn intern_n_node(pers: &PersTier, st: &mut AState, v: NNodeView) -> Result<NIdx, CheckError> {
    st.store.intern_name(pers, v)
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Denote.lean:76-83 denoteNAux` — the
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
/// Lean twin: `proof/ConRon/Arena/Denote.lean:87-88 denoteN` — the readback of
/// a name handle, at the store's own node count as fuel.
pub fn denote_n(pers: &PersTier, st: &NStore, h: &NIdx) -> Option<Name> {
    denote_n_aux(pers, st, st.node_count(pers) as u64 + 1, h)
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:194-198 readName` — read a name
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:204-209 readNames` — read a LIST
/// of name handles back.  The twin spells the `List` recursion as its own
/// helper because `ks.mapM readName` is a closure (DESIGN.md §3.4); the Rust
/// spells the same recursion over a `Vec` by a cursor, which is §3.4's own
/// rule and `-loops-to-rec`'s shape.
pub fn read_names(pers: &PersTier, st: &AState, ks: &Vec<NIdx>) -> Result<Vec<Name>, CheckError> {
    read_names_from(pers, st, ks, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:204-209 readNames` — the cursor
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:213-221 internName` — intern a
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

/// con-leche: ConLeche/Kernel/Expr.lean:40-53 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:226-230 viewL` — decode a level
/// handle.
pub fn view_l(pers: &PersTier, st: &AState, h: &LIdx) -> Result<LNodeView, CheckError> {
    match st.store.ls().view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_L))),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:40-53 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:235-237 derivedL` — the level's
/// derived pair (its 32-bit hash and its `hasParam` bit, the computed field at
/// lines 47-53), read in `O(1)`.  Total, so no `Result` (module note).
pub fn derived_l(pers: &PersTier, st: &AState, h: &LIdx) -> LDer {
    st.store.lder(pers, h)
}

/// con-leche: none — hash-cons a level node, through the nesting
/// Lean twin: `proof/ConRon/Arena/Monad.lean:240-251 internLNode` (the
/// capacity test is one layer down here; see `intern_e`).
pub fn intern_l_node(pers: &PersTier, st: &mut AState, v: LNodeView) -> Result<LIdx, CheckError> {
    st.store.intern_level(pers, v)
}

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Denote.lean:118-128 denoteLAux` — the
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

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Denote.lean:131-132 denoteL` — the readback
/// of a level handle, at the store's own node count as fuel.
pub fn denote_l(pers: &PersTier, st: &LStore, h: &LIdx) -> Option<Level> {
    denote_l_aux(pers, st, st.node_count(pers) as u64 + 1, h)
}

/// con-leche: none — `denoteL` mapped over a level-handle list
/// Lean twin: `proof/ConRon/Arena/Denote.lean:169-171 denoteLList` — a list
/// node's children are level handles only, so there is no recursion through
/// `LsIdx` and no fuel.  The `List` recursion is a cursor over the `Vec`.
pub fn denote_l_list(pers: &PersTier, st: &LStore, us: &Vec<LIdx>) -> Option<Vec<Level>> {
    denote_l_list_from(pers, st, us, 0, Vec::new())
}

/// con-leche: none — `denoteL` mapped over a level-handle list
/// Lean twin: `proof/ConRon/Arena/Denote.lean:169-171 denoteLList` — the
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
/// Lean twin: `proof/ConRon/Arena/Denote.lean:174-177 denoteLs`.
pub fn denote_ls(pers: &PersTier, st: &LsStore, h: &LsIdx) -> Option<Vec<Level>> {
    match st.view(pers, h) {
        None => None,
        Some(us) => denote_l_list(pers, &st.ls, &us),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:258-262 readLevel` — **the
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

/// con-leche: ConLeche/Kernel/Expr.lean:40-53 Level
/// Lean twin: `proof/ConRon/Arena/Monad.lean:266-278 internLevel` — intern a
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

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Monad.lean:287-291 viewLs` — decode a
/// universe-argument list handle (the `const` node's second field, line 347).
pub fn view_ls(pers: &PersTier, st: &AState, h: &LsIdx) -> Result<LsNodeView, CheckError> {
    match st.store.ls_s().view(pers, h) {
        Some(v) => Ok(v),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_LS))),
    }
}

/// con-leche: none — hash-cons a universe-argument list
/// Lean twin: `proof/ConRon/Arena/Monad.lean:294-305 internLsNode` (the
/// capacity test is one layer down here; see `intern_e`).
pub fn intern_ls_node(
    pers: &PersTier,
    st: &mut AState,
    v: LsNodeView,
) -> Result<LsIdx, CheckError>  {
    st.store.intern_levels(pers, v)
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:309-313 readLevels` — read a
/// universe argument list back as transient `Level` trees.
pub fn read_levels(pers: &PersTier, st: &AState, h: &LsIdx) -> Result<Vec<Level>, CheckError> {
    match denote_ls(pers, st.store.ls_s(), h) {
        Some(us) => Ok(us),
        None => fail(CheckError::Internal(code_points(&M_DANGLING_LS))),
    }
}

/// con-leche: none — intern a list of transient levels, one handle each
/// Lean twin: `proof/ConRon/Arena/Monad.lean:316-320 internLevelList`.
pub fn intern_level_list(
    pers: &PersTier,
    st: &mut AState,
    us: &Vec<Level>,
) -> Result<Vec<LIdx>, CheckError>  {
    intern_level_list_from(pers, st, us, 0, Vec::new())
}

/// con-leche: none — intern a list of transient levels, one handle each
/// Lean twin: `proof/ConRon/Arena/Monad.lean:316-320 internLevelList` — the
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:325-327 internLevels`.
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
// `intern_ls_node` that append to the PERSISTENT tier whatever tier the store
// is in, over `arena::store`'s `intern_persistent` family.  The capacity test
// is the same one against the persistent array and the error is the same
// `Native` kind — and, as with `intern_e`, the test sits one layer down here
// (the twin's `internPersistentE` tests `sizeOf v < Idx.idxCap` at the
// wrapper; `EStore::intern_persistent` already *is* that test).
// `arena::promote` is the only caller.

/// con-leche: none — arena infrastructure; hash-cons an expression node into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:348-358 internPersistentE`.
pub fn intern_persistent_e(
    pers: &PersTier,
    st: &mut AState,
    v: ENodeView,
) -> Result<EIdx, CheckError>  {
    st.store.intern_persistent(pers, v)
}

/// con-leche: none — arena infrastructure; hash-cons a name node into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:361-371 internPersistentN`, through
/// the nesting.
pub fn intern_persistent_n(
    pers: &PersTier,
    st: &mut AState,
    v: NNodeView,
) -> Result<NIdx, CheckError>  {
    st.store.intern_name_persistent(pers, v)
}

/// con-leche: none — arena infrastructure; hash-cons a level node into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:374-384 internPersistentL`, through
/// the nesting.
pub fn intern_persistent_l(
    pers: &PersTier,
    st: &mut AState,
    v: LNodeView,
) -> Result<LIdx, CheckError>  {
    st.store.intern_level_persistent(pers, v)
}

/// con-leche: none — arena infrastructure; hash-cons a universe-argument list into the persistent tier
/// Lean twin: `proof/ConRon/Arena/Monad.lean:387-397 internPersistentLs`, through
/// the nesting.
pub fn intern_persistent_ls(
    pers: &PersTier,
    st: &mut AState,
    v: LsNodeView,
) -> Result<LsIdx, CheckError>  {
    st.store.intern_levels_persistent(pers, v)
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:338-341 inst1Get` — probe the
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:343-348 inst1Set` — record an
/// `instantiate1` answer.
pub fn inst1_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst1_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:351-353 inst1Clear` — the memo is
/// "dropped after each call, since it also depends on `v`".
pub fn inst1_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst1_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:357-360 instLGet` — probe the
/// `instantiateList` memo.
pub fn inst_l_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.inst_l_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:362-367 instLSet` — record an
/// `instantiateList` answer.
pub fn inst_l_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst_l_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:370-372 instLClear` — drop the
/// `instantiateList` memo (it depends on `vs`).
pub fn inst_l_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst_l_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:376-379 liftGet` — probe the
/// `liftLooseBVars` memo.
pub fn lift_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.lift_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:381-386 liftSet` — record a
/// `liftLooseBVars` answer.
pub fn lift_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.lift_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:389-391 liftClear` — drop the
/// `liftLooseBVars` memo (it depends on `amount`).
pub fn lift_clear(st: &mut AState) {
    reset_map(&mut st.memos.lift_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:395-398 resetGet` — probe the
/// `resetMeta` memo.
pub fn reset_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.reset_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:400-405 resetSet` — record a
/// `resetMeta` answer.
pub fn reset_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.reset_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:408-410 resetClear` — drop the
/// `resetMeta` memo.
pub fn reset_clear(st: &mut AState) {
    reset_map(&mut st.memos.reset_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:414-417 renameGet` — probe the
/// `renameConsts` memo.
pub fn rename_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.rename_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:419-424 renameSet` — record a
/// `renameConsts` answer.
pub fn rename_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.rename_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1109-1111 renameConstsFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:427-429 renameClear` — drop the
/// `renameConsts` memo (it depends on the renaming).
pub fn rename_clear(st: &mut AState) {
    reset_map(&mut st.memos.rename_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go
/// Lean twin: `proof/ConRon/Arena/Monad.lean:433-436 abs1Get` — probe the
/// `abstract1` memo.
pub fn abs1_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.abs1_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go
/// Lean twin: `proof/ConRon/Arena/Monad.lean:438-443 abs1Set` — record an
/// `abstract1` answer.
pub fn abs1_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.abs1_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1927-1929 abstract1Fast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:446-448 abs1Clear` — drop the
/// `abstract1` memo (it depends on `d`).
pub fn abs1_clear(st: &mut AState) {
    reset_map(&mut st.memos.abs1_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:452-455 lowerGet` — probe the
/// `lowerBVars` memo.
pub fn lower_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.lower_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:457-462 lowerSet` — record a
/// `lowerBVars` answer.
pub fn lower_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.lower_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2144-2146 lowerBVarsFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:465-467 lowerClear` — drop the
/// `lowerBVars` memo (it depends on `amount`).
pub fn lower_clear(st: &mut AState) {
    reset_map(&mut st.memos.lower_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:471-474 inst1LGet` — probe the
/// `instantiate1Lift` memo.
pub fn inst1_l_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.inst1_l_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:476-481 inst1LSet` — record an
/// `instantiate1Lift` answer.
pub fn inst1_l_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst1_l_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2356-2358 instantiate1LiftFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:484-486 inst1LClear` — drop the
/// `instantiate1Lift` memo (it depends on `v`).
pub fn inst1_l_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst1_l_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:490-493 instLPGet` — probe the
/// level-substitution memo.
pub fn inst_lp_get(st: &AState, k: &EIdxNat) -> Option<EIdx> {
    match st.memos.inst_lp_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:495-500 instLPSet` — record a
/// level-substitution answer.
pub fn inst_lp_set(st: &mut AState, k: EIdxNat, r: &EIdx) {
    st.memos.inst_lp_c.insert(k, r.dup2());
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2718-2720 Expr.instLPFast
/// Lean twin: `proof/ConRon/Arena/Monad.lean:503-505 instLPClear` — drop the
/// level-substitution memo (it depends on `ks` and `us`).
pub fn inst_lp_clear(st: &mut AState) {
    reset_map(&mut st.memos.inst_lp_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:509-512 bvarBGet` — probe the
/// loose-bvar-bound memo.
pub fn bvar_b_get(st: &AState, k: &EIdx) -> Option<u64> {
    match st.memos.bvar_b_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:514-519 bvarBSet` — record a
/// loose-bvar bound.
pub fn bvar_b_set(st: &mut AState, k: EIdx, r: u64) {
    st.memos.bvar_b_c.insert(k, r);
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1394-1395 bvarBoundMemo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:522-524 bvarBClear` — drop the
/// loose-bvar-bound memo.
pub fn bvar_b_clear(st: &mut AState) {
    reset_map(&mut st.memos.bvar_b_c)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:528-531 fvarBGet` — probe the
/// fvar-range memo.
pub fn fvar_b_get(st: &AState, k: &EIdx) -> Option<u64> {
    match st.memos.fvar_b_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:533-538 fvarBSet` — record an
/// fvar range.
pub fn fvar_b_set(st: &mut AState, k: EIdx, r: u64) {
    st.memos.fvar_b_c.insert(k, r);
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1424-1425 fvarRangeMemo
/// Lean twin: `proof/ConRon/Arena/Monad.lean:541-543 fvarBClear` — drop the
/// fvar-range memo.
pub fn fvar_b_clear(st: &mut AState) {
    reset_map(&mut st.memos.fvar_b_c)
}
