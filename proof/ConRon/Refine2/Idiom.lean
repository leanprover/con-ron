/-
# `ConRon.Refine2.Idiom` — the machine words, and the three changes the idiom needed

**THEOREM 2 of DESIGN.md §8.2**, the Aeneas refinement of the Rust arena
checker against the Lean twin (B).  This is the bottom of the tower: the
scalar conversions every later abstraction is written with, and the three
things task #97s round 3 measured that the `Refine` tier's idiom does not
already carry.

## What round 3 asked for, and where it is

| round 3's ask | here |
|---|---|
| `(splits := 40)` rather than `rust_grind`'s fixed `(ematch := 12) (gen := 24)` | `rust_grind2` |
| `attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp` — a SOUNDNESS trap, and **it does not travel through an import** | `grind_ext_off`, and the line is repeated at the top of every file of this tier |
| a fuel shape step per recursive function, ~12 lines | per function, in `Refine2/ExprOps/*` |

**Why the `-grind` line is not optional.**  Aeneas registers those two as
`@[grind ext]` (`Aeneas/Std/Scalar/Core.lean:778`, `:903`), so every
machine-word disequality — and `split`ting a generated `if tag = TAG_APP`
produces one per arm — is blasted into `∀ i, x.bv[i] = y.bv[i]`.  On an
`@[irreducible]` generated constant (`arena.handle.ETAG_BVAR : U32 := 0#u32`)
`grind`'s `lia` module then closes the goal with a `decide`-by-`rfl` step the
*elaborator* evaluates to `false` and the *kernel* to `true`; the tactic
reports success and the declaration is rejected afterwards.  Erasing the two
`ext` registrations removes it.

## Why this tier does NOT split `Refine/Abs.lean`

Round 3's third recommendation was to split `Refine/Abs.lean` into
`Refine/Idiom.lean` (the macros, importing only Aeneas) and the rest, so that
(B)'s proofs get the idiom without `ConRon.Generated`'s 105 k lines.  That is
P3's saving, not P5's: **Theorem 2 is a statement ABOUT the generated model**,
so every file here imports `ConRon.Generated` anyway and the split would buy
this tier nothing.  `ConRon.Refine.Abs` is imported whole, which also brings
the `expr.*` / `name.*` / `level.*` inversion lemmas the pinned-data tier
proved — and which this tier reuses at `absBinderMeta` and `absLiteral`.
-/
import ConRon.Refine.Abs
import ConRon.Refine.Nat
import ConRon.Arena.Monad

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

/-! ## The two `@[grind ext]` registrations, erased

`attribute [-grind]` is file-local: it must be repeated at the top of every
file that closes a goal with `grind`.  This is the canonical spelling; see the
module note for why it is a soundness matter and not a performance one. -/
attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

/-- The closing call of this tier: `rust_grind`'s budget with one more
case-split allowance.  Round 3 measured `rust_grind`'s default one split short
of the arena's body — ten branches, three `Option` matches and four `Result`
binds in one arm is more splitting than a `Level` leaf — and `AUTOMATION.md`'s
rule is that this is a default to raise, not a per-lemma override. -/
macro "rust_grind2" : tactic =>
  `(tactic| grind (ematch := 12) (gen := 24) (splits := 40))

/-- `rust_grind2` with the lemma list a caller wants to add, for the arms
whose callee set is not in the ambient `@[grind →]` layer. -/
syntax "rust_grind2" "[" Lean.Parser.Tactic.grindParam,* "]" : tactic
macro_rules
  | `(tactic| rust_grind2 [$ts,*]) =>
    `(tactic| grind (ematch := 12) (gen := 24) (splits := 40) [$ts,*])

/-! ## The machine words

DESIGN §8.3's handles are `u32` words on both sides and DESIGN §8.4's counters
are `u64` against the twin's `Nat`, so the conversions are four functions and
their `toNat` equations.  Everything below is stated forward from `= ok`, as
§3.5 asks. -/

/-- A Rust `u32` as the twin's `UInt32`.  The twin's handle word IS a
`UInt32` (`Arena/Handle.lean`'s `Idx.word`), so this is the whole of the
handle abstraction. -/
def absU32 (x : Std.U32) : UInt32 := UInt32.ofNat x.val

/-- A Rust `u64` as the twin's `UInt64` — the derived words. -/
def absU64 (x : Std.U64) : UInt64 := UInt64.ofNat x.val

/-- A Rust `u64` counter as the twin's `Nat`: the fuel, the de Bruijn
indices, the cursors. -/
abbrev absU (x : Std.U64) : Nat := x.val

/-- A Rust `usize` as the twin's `Nat`. -/
abbrev absSz (x : Std.Usize) : Nat := x.val

theorem u32_val_lt (x : Std.U32) : x.val < 4294967296 := by scalar_tac

theorem u64_val_lt (x : Std.U64) : x.val < 18446744073709551616 := by scalar_tac

@[simp] theorem absU32_toNat (x : Std.U32) : (absU32 x).toNat = x.val :=
  UInt32.toNat_ofNat_of_lt' (u32_val_lt x)

@[simp] theorem absU64_toNat (x : Std.U64) : (absU64 x).toNat = x.val :=
  UInt64.toNat_ofNat_of_lt' (u64_val_lt x)

theorem absU32_inj : Function.Injective absU32 := by
  intro x y h
  apply UScalar.eq_imp
  rw [← absU32_toNat x, ← absU32_toNat y, h]

theorem absU64_inj : Function.Injective absU64 := by
  intro x y h
  apply UScalar.eq_imp
  rw [← absU64_toNat x, ← absU64_toNat y, h]

/-- Equality of `u32`s is equality of the abstractions — the `==` every
handle comparison of the port is. -/
@[simp] theorem absU32_eq_iff (x y : Std.U32) : absU32 x = absU32 y ↔ x = y :=
  ⟨fun h => absU32_inj h, fun h => by rw [h]⟩

@[simp] theorem absU64_eq_iff (x y : Std.U64) : absU64 x = absU64 y ↔ x = y :=
  ⟨fun h => absU64_inj h, fun h => by rw [h]⟩

/-! ### The three word operations the handle layout uses

`Arena/Handle.lean` writes the packing with `*`, `/` and `%` by powers of two
rather than with `>>>`/`&&&` (its own module note says why: every roundtrip
lemma is then `omega`), and `arena::handle` does the same.  So the abstraction
has to commute with exactly three operations. -/

theorem absU32_div {x y z : Std.U32} (h : x / y = ok z) :
    absU32 x / absU32 y = absU32 z := by
  have hv := ConRon.Refine.Nat.udiv_val h
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_div, absU32_toNat, absU32_toNat, absU32_toNat, hv]

theorem absU32_mod {x y z : Std.U32} (h : x % y = ok z) :
    absU32 x % absU32 y = absU32 z := by
  have hv := ConRon.Refine.Nat.urem_val h
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mod, absU32_toNat, absU32_toNat, absU32_toNat, hv]

theorem absU32_add {x y z : Std.U32} (h : x + y = ok z) :
    absU32 x + absU32 y = absU32 z := by
  have hv := ConRon.Refine.Nat.uadd_val h
  have hz := u32_val_lt z
  have hb : x.val + y.val < 2 ^ 32 := by
    rw [show (2 : Nat) ^ 32 = 4294967296 from by norm_num]; omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, absU32_toNat, absU32_toNat, absU32_toNat, hv,
    Nat.mod_eq_of_lt hb]

theorem absU32_mul {x y z : Std.U32} (h : x * y = ok z) :
    absU32 x * absU32 y = absU32 z := by
  obtain ⟨-, hv⟩ := ConRon.Refine.Nat.umul_val h
  have hz := u32_val_lt z
  have hb : x.val * y.val < 2 ^ 32 := by
    rw [show (2 : Nat) ^ 32 = 4294967296 from by norm_num]; omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_mul, absU32_toNat, absU32_toNat, absU32_toNat, hv,
    Nat.mod_eq_of_lt hb]

/-! ### The `u64` counters against the twin's `Nat`

These are the shape the fuel step wants: a Rust `fuel - 1` is the twin's
`fuel` at `absU fuel = m + 1`, and a Rust `d + 1` is the twin's `d + 1`. -/

theorem absU_sub_one {x z : Std.U64} (h : x - 1#u64 = ok z) :
    1 ≤ absU x ∧ absU z = absU x - 1 := by
  obtain ⟨hle, hv⟩ := ConRon.Refine.Nat.usub_val h
  exact ⟨by simpa using hle, by simpa using hv⟩

theorem absU_add_one {x z : Std.U64} (h : x + 1#u64 = ok z) :
    absU z = absU x + 1 := by
  have hv := ConRon.Refine.Nat.uadd_val h
  simpa using hv

theorem absSz_add_one {x z : Std.Usize} (h : x + 1#usize = ok z) :
    absSz z = absSz x + 1 := by
  have hv := ConRon.Refine.Nat.uadd_val h
  simpa using hv

theorem absSz_sub {x y z : Std.Usize} (h : x - y = ok z) :
    absSz y ≤ absSz x ∧ absSz z = absSz x - absSz y :=
  ConRon.Refine.Nat.usub_val h

end ConRon.Refine2
