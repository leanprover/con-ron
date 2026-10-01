//! Port of `ConLeche/Kernel/ExprOps.lean` — the term operations.
//!
//! Everything the checker does *to* a term that is not building or comparing
//! one (`crate::kernel::expr`): opening and closing binders (`instantiate1`,
//! `instantiateList`, `abstract1`, `abstractRange`), shifting loose bound
//! variables (`liftLooseBVars`, `lowerBVars`, `instantiate1Lift`), reading
//! spines and telescopes (`getAppFn`, `getAppArgs`, `stripPis`, `instPisAt`
//! and friends), and the *exact* derived-field accessors `bvarB`/`fvarB`
//! with the memoized walks behind their saturated branch.
//!
//! **The `@[csimp]` families.**  con-leche writes each of these walks twice:
//! a plain structural `def` (the specification every proof consumes) and a
//! memoized `*Go`/`*Fast` pair that a `@[csimp]` lemma substitutes for it in
//! compiled code.  The port implements the **`*Fast`** member — that is what
//! con-leche executes — and cites the logical definition, the `*Go` walk, the
//! `*Fast` wrapper and the `@[csimp]` lemma together; the lemma *is* the
//! transparency argument for the deviation, since it is a kernel-checked
//! equation between the two, so the port's single function refines the
//! logical definition by that equation.  Nine families are folded this way
//! (`instantiate1`, `instantiateList`, `liftLooseBVars`, `resetMeta`,
//! `abstract1`, `lowerBVars`, `instantiate1Lift`, `renameConsts` and
//! `instantiateLevelParams`), plus `hasFvar` and `looseBVarsBounded`, whose
//! `*Fast` members are not walks at all but `O(1)` reads of the packed word.
//!
//! **Memos.**  Every memo in this file is *local*: con-leche creates it
//! empty (`{}`) inside the `*Fast` wrapper and drops it when the call
//! returns, because the answer also depends on the parameters that are not
//! in the key (`v`, `vs`, `amount`, `d`, `f`, `ks`/`us`).  The port does the
//! same — a `crate::ron::hashmap::HashMap` local to the wrapper, handed to the
//! walk as a `&mut` parameter.  `&mut` rather than Lean's threaded
//! `(result, memo)` pair because Aeneas's back-end translates a `&mut`
//! parameter into exactly that threaded pair, so the generated Lean carries
//! the cited signature; DESIGN.md §3.4 reserves `&mut` for the state
//! parameter, and the memo is precisely this walk's state.  (The memo tables
//! that live in `CState` are `ConLeche/Cached/*`'s business, not this
//! file's; none of them appears here.)
//!
//! Conventions, as in `expr.rs`: terms come in by shared reference and go
//! out owned, with an explicit `dup` (a `P` bump) wherever Lean returns a
//! subterm or an unchanged node; Lean's `List` is a `Vec` walked by an index
//! helper (`*_from`, DESIGN.md §3.4); the `Nat` indices and cutoffs are
//! `u64` (§3.3), with `sub_nat` for the truncated subtractions Lean's `Nat`
//! performs and Rust's `u64` would fail on.  Higher-order arguments are
//! one-method traits (`NameToName` here), the pattern task #9 fixed.
//!
//! Order follows the Lean file; where a `@[csimp]` family's members are far
//! apart the single Rust item sits at the *logical* definition's position,
//! which is why `abstract1`, `lower_bvars` and `instantiate1_lift` use
//! `fvar_b`/`bvar_b` before this file defines them.

use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::expr::ExprView;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;
use crate::kernel::name;

// ---------------------------------------------------------------------------
// Small helpers with no Lean counterpart
// ---------------------------------------------------------------------------

/// con-leche: none — Lean's `Nat` subtraction, which truncates at zero
/// `a - b` as Lean's `Nat` computes it.  Rust's `-` on `u64` underflows (a
/// `fail` in the Aeneas model), so every place the cited Lean subtracts
/// without a guard that keeps the result non-negative goes through this:
/// `bvarBound`'s `body.bvarBound - 1`, `instSpine`'s `t - 1` and
/// `recRulePlain`'s `mI - 1 - k`.  Where the Lean arm *does* carry the guard
/// (`instantiate1`'s `i > d` before `.bvar (i - 1)`, `lowerBVars`'s
/// `i ≥ c + amount` before `.bvar (i - amount)`) the port subtracts
/// directly, as the cited code does.
pub fn sub_nat(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        0
    }
}

/// con-leche: none — the memo key of `Std.HashMap (Expr × Nat) Expr`
/// The `(node, cursor)` key five of this file's memos use.  Lean's `Prod`
/// carries derived `BEq`/`Hashable` instances; here they are the two
/// dictionaries below (task #7's `Eq2`/`Hashable`, not `core::cmp`).
pub struct ExprNatKey {
    pub e: Expr,
    pub d: u64,
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
/// The derived `Hashable (Expr × Nat)`.  Hash values are verdict-neutral
/// (DESIGN.md §3.2), so the crate's own `Expr` hash is what goes in.
impl Hashable for ExprNatKey {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(expr::hash(&self.e), name::nat_hash(self.d))
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
/// The derived `BEq (Expr × Nat)`: the node by `Expr.beq` (pointer test,
/// packed word, descent), then the cursor.
impl Eq2 for ExprNatKey {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &Self) -> bool {
        if expr::beq(&self.e, &other.e) {
            self.d == other.d
        } else {
            false
        }
    }
}

// ---------------------------------------------------------------------------
// Memoise only what is shared (`ExprOpsC.lean`, "The memo"; `Exclusive.lean`)
// ---------------------------------------------------------------------------
//
// The six functions below are the whole of con-leche's task #317/#319 memo
// discipline as this port expresses it: a walk reads the exclusivity of the
// BORROWED node it is about to rebuild and hands the answer to a probe and a
// record, which spend nothing at all on an exclusive node — no key, no hash,
// no bucket, no stored `dup`.  A node with one reference cannot be reached
// twice by the walk that is inside its only parent, so an entry for it can
// never be read.
//
// **Task #97-SWAP-2 left them without a reader of the count.**  The count
// read was `ron::node::is_exclusive`, and that module went with the tagged
// handle; `ron::ptr`'s four operations do not include one (DESIGN.md §3.2),
// and the model's answer was `false` either way.  So `excl` is a parameter
// here and nothing in the crate computes a `true` for it any more — the
// callers these were written for were the `Expr`-tree walks, retired at task
// #97-SWAP, and the arena has its own store-level discipline.
//
// **They exist so that the key is built on the shared path only.**  A
// `KEY = expr_nat_key(e, d)` in front of the branch would be a second share
// of `e` (`expr_nat_key` takes the node by a `dup`), and the exclusivity read
// above it would then be answering about the key rather than about the term —
// con-leche's borrowed-parameter requirement, in the one shape Rust can
// violate it.  Hence `e` and the cursor, never a prebuilt key.
//
// **In the model `excl` is `false`** — it was `ron::node::is_exclusive`,
// modelled `ok false`, and since task #97-SWAP-2 there is no such read at all
// — so each of these is definitionally its unguarded predecessor and the
// walks' refinement lemmas are the ones this port already had.

// ---------------------------------------------------------------------------
// Sizes, abstraction, scope predicates (`ExprOps.lean:741-913`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:954-960 isLam
/// Is the expression a λ?
pub fn is_lam(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Lam(_, _, _) => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// `allLevelParamsDefined` (`Level.lean:251-412`), the second `Expr` operation
// spelled in `Kernel/Level.lean` for import order (task #13's note).  Task
// #24 needed it — `checkConstantVal` asks it of every declaration's type —
// and task #13 had left it owed.
// ---------------------------------------------------------------------------

/* Not ported from `ExprOps.lean` (DESIGN.md §3.1: the `theorem`s are the
   spec this port will be proved against, not part of it):

   * the eleven memo invariants — `Inst1MemoInv` (:60), `InstLMemoInv`
     (:247), `LiftMemoInv` (:410), `ResetMemoInv` (:561), `RenameMemoInv`
     (:980), `MemoBInv` (:1494), `MemoFInv` (:1615), `Abs1MemoInv` (:1769),
     `LowerMemoInv` (:1992), `Inst1LMemoInv` (:2202) and `ILPMemoInv`
     (:2543) — and their `empty`/`insert` lemmas.  They are `Prop`s ("every
     recorded answer is the real one"); Charon erases `Prop`s, and these are
     exactly the invariants the Rust-side refinement proof will restate
     about `crate::ron::hashmap` memos.
   * every `theorem`: the `*Go_spec` soundness lemmas, the eleven `@[csimp]`
     equations (each cited on the item it licenses), `sizeB_instantiate1`
     (:750), `looseBVarsBounded_iff` (:1305), `hasFvar_eq_false_iff` (:1325),
     `fvarRange_bne_zero` (:1332), `bvarBRaw_exact` (:1453),
     `fvarBRaw_exact` (:1587), `bvarB_eq`/`fvarB_eq`,
     `abstract1_of_fvarRange_le` (:1762), `lowerBVars_of_bvarBound_le`
     (:1956), `instantiate1Lift_of_bvarBound_le` (:2166),
     `Level.subst_eq_self` (:2408), `Level.allParamsDefined_of_not_hasParam`
     (:2414), `Level.substPW_eq_self` (:2439),
     `PropWhen.paramsDefined_of_not_hasParams` (:2450),
     `Expr.instantiateLevelParams_eq_self` (:2462),
     `Expr.levelHasParam_eq`/`levelsHaveParam_eq`/`hasLP_eq`, and
     `Expr.allLevelParamsDefined_of_not_hasLevelParam` (:2727).
   * `Level.hasParam` (:2399) is not a new function: it is the spec
     recurrence of `Expr.levelHasParam`, which task #3 ported as
     `level::level_has_param`; the citation for it sits there. */
