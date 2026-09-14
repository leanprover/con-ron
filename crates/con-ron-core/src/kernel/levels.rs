//! con-leche: none — the representation of `Expr.const`'s `List Level`
//! (DESIGN.md §3.2); Lean's list has no counterpart to this shape.
//!
//! **The level list of a constant reference, without a heap block for the
//! common cases** (task #93).
//!
//! `Expr.const` carries a `List Level` in con-leche, which the port held as
//! `P<Vec<Level>>` from task #38 on: a handle whose block is 16 + 24 = 40
//! bytes (a 48-byte size class, DESIGN.md §3.2) *plus* the `Vec`'s own
//! `8·n`-byte array — **two allocations per constant reference, even for a
//! monomorphic constant whose list is empty**.  The census of task #93 (the
//! DESIGN.md entry has it) says what that buys: on `core`, of the constant
//! references live at the install boundary the overwhelming majority carry
//! **no** level at all and almost all of the rest carry exactly one.
//!
//! So this type spends a tag and one word:
//!
//! ```ignore
//! enum Levels { Zero, One(Level), Many(P<Vec<Level>>) }   // 16 bytes
//! ```
//!
//! `Zero` allocates nothing; `One` holds the level's *own* shared handle, so
//! it allocates nothing either; only `Many` keeps the boxed list, and only
//! for two levels or more.  `ExprKind::Const(Name, Levels)` is therefore a
//! 24-byte arm — narrower than `Lam`/`ForallE`'s 32 — so `ExprKind` stays 40,
//! `ExprNode` 48 and its `P` block 64, which is the size class task #92
//! measured con-ron's node into.  **A fourth constructor would not pay**: a
//! `Two(Level, Level)` arm is 24 bytes on its own, which makes `Const` 32,
//! `ExprKind` 48, `ExprNode` 56 and the block 80 — one whole class up, for
//! every node in the heap.
//!
//! # The canonical form, and why `beq` may compare tags
//!
//! [`of_vec`] is the **only** way a `Levels` is built from a list, and it
//! picks the narrowest constructor that fits: `Zero` for the empty list,
//! `One` for a singleton, `Many` only for two or more.  So a well-formed
//! `Levels` has `Many`'s `Vec` at length ≥ 2 and the constructor is a
//! function of the length — which is what lets [`beq`] answer `false` on two
//! different constructors without looking inside, and [`len`] answer in `O(1)`.
//! That is the same discipline `prop_when` states for its five-constructor
//! representation, and the same shape of obligation: the Lean-side
//! `LevelsWF` of `Refine/Abs.lean` carries the length clause, and under it
//! `abs` is injective and `beq` is equality (DESIGN.md §3.5).
//!
//! # Conventions
//!
//! As in `name.rs`, `level.rs` and `expr.rs`: a `Level` comes in by shared
//! reference and goes out owned ([`dup`] for every share); Lean's `List` is a
//! `Vec` walked by an index (no loops, DESIGN.md §3.4); the *value* of every
//! observation here — [`hash`], [`have_param`], [`len`], [`head_d`] — is the
//! value the corresponding `Vec<Level>` function of `level.rs` gives for the
//! same list, constructor by constructor, so nothing a hash word or a memo
//! bucket depends on moves.
//!
//! **This module sits directly above `level.rs` and below `expr.rs`**, and
//! uses nothing else.  The three-constructor dispatches that need a function
//! from higher up therefore live where that function does, not here:
//! `expr::const_levels_beq` (`beqGo`'s `.const` arm), `expr_ops`'s
//! `const_levels_subst` and `const_levels_all_params_defined`, and
//! `state_c::is_equiv_list_c_m` (the memoised universe check).

use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::ron::ptr;
use crate::ron::ptr::P;

/// con-leche: none — `Expr.const`'s `List Level`, in the port's shape (DESIGN.md §3.2)
/// The level arguments of a constant reference: nothing, one level, or a
/// shared list of two or more.  See the module note for the canonical form
/// [`of_vec`] establishes and every operation below relies on.
pub enum Levels {
    Zero,
    One(Level),
    Many(P<Vec<Level>>),
}

/// con-leche: none — the canonical form of a `List Level` (the module note)
/// The list, in the narrowest constructor that holds it.  The **only**
/// builder: `Many` is never handed a list shorter than two, so the
/// constructor is a function of the length.
pub fn of_vec(us: Vec<Level>) -> Levels {
    if us.len() == 0 {
        Levels::Zero
    } else if us.len() == 1 {
        Levels::One(level::dup(&us[0]))
    } else {
        Levels::Many(ptr::new(us))
    }
}

/// con-leche: none — the `List Level` back out of the canonical form
/// The list as a fresh `Vec`, one `P` bump per level — the reverse of
/// [`of_vec`], and what a reader that really does need a `Vec<Level>` calls.
pub fn to_vec(ls: &Levels) -> Vec<Level> {
    match ls {
        Levels::Zero => Vec::new(),
        Levels::One(u) => one_vec(level::dup(u)),
        Levels::Many(us) => vec_copy(us),
    }
}

/// con-leche: none — a one-element `Vec<Level>`, spelled without a literal
/// `vec![u]` is a macro Charon does not see through; this is the same value.
pub fn one_vec(u: Level) -> Vec<Level> {
    let mut out: Vec<Level> = Vec::with_capacity(1);
    out.push(u);
    out
}

/// con-leche: none — a `Vec<Level>` copy; Lean's `List Level` is shared by value
/// `Many`'s payload copied out: the entry point of the index recursion below.
/// The same walk as `expr_ops::levels_copy`, spelled here so that this module
/// depends on nothing above `level.rs` — every other module that holds a
/// `Levels` is above this one, and a `use` cycle would be the only way round.
pub fn vec_copy(us: &Vec<Level>) -> Vec<Level> {
    vec_copy_from(us, 0, Vec::with_capacity(us.len()))
}

/// con-leche: none — the index recursion behind `vec_copy`
/// The accumulator is passed by value and returned (task #6's rule).
pub fn vec_copy_from(us: &Vec<Level>, i: usize, out: Vec<Level>) -> Vec<Level> {
    if i >= us.len() {
        out
    } else {
        let mut out = out;
        out.push(level::dup(&us[i]));
        vec_copy_from(us, i + 1, out)
    }
}

/// con-leche: none — the `P` bump that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a level list: `Zero` is a tag, `One` dups the level's handle,
/// `Many` bumps the list's handle — never a copy of the array.
pub fn dup(ls: &Levels) -> Levels {
    match ls {
        Levels::Zero => Levels::Zero,
        Levels::One(u) => Levels::One(level::dup(u)),
        Levels::Many(us) => Levels::Many(ptr::clone(us)),
    }
}

/// con-leche: none — `List.length` of `Expr.const`'s levels
/// How many levels: `O(1)` on the canonical form, since the constructor is a
/// function of the length (the module note).
pub fn len(ls: &Levels) -> usize {
    match ls {
        Levels::Zero => 0,
        Levels::One(_) => 1,
        Levels::Many(us) => us.len(),
    }
}

/// con-leche: none — `us[0]` of `Expr.const`'s levels, with a default
/// The first level, shared; `Level.zero` where there is none.  The `_d`
/// suffix is `struct_parts::sort_get_d`'s: a total reader with a default
/// rather than a panic (DESIGN.md §3.4 forbids a panic as control flow), and
/// every caller guards on [`len`] first, so the default is unreachable.
pub fn head_d(ls: &Levels) -> Level {
    match ls {
        Levels::Zero => level::zero(),
        Levels::One(u) => level::dup(u),
        Levels::Many(us) => level::dup(&us[0]),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:124-127 levelsHaveParam
/// `levelsHaveParam` on the canonical form: the same value as
/// `level::levels_have_param` on [`to_vec`], with no `Vec` built.
pub fn have_param(ls: &Levels) -> bool {
    match ls {
        Levels::Zero => false,
        Levels::One(u) => level::level_has_param(u),
        Levels::Many(us) => level::levels_have_param(us),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:136-139 levelsHash
/// `levelsHash` on the canonical form.  The cited `List` fold ends at `13`
/// and mixes right to left, so a singleton is `mixHash (levelHash u) 13` —
/// **the hash word of a `.const` node is unchanged by this representation**,
/// which is what the memo buckets and `beq`'s word test depend on.
pub fn hash(ls: &Levels) -> u64 {
    match ls {
        Levels::Zero => 13,
        Levels::One(u) => name::mix_hash(level::level_hash(u), 13),
        Levels::Many(us) => level::levels_hash(us),
    }
}
