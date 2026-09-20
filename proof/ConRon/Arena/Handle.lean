/-
# The arena's handles (DESIGN.md §8.3, task #97 P2a)

One 32-bit word per handle:

    bits 31…28   ctor tag   (4 bits, high)
    bit  27      tier       (0 = persistent, 1 = scratch)
    bits 26…0    index      into THAT CONSTRUCTOR'S array of THAT TIER

so 134 217 728 nodes per constructor per tier, and — the point of putting
the tier *above* the index rather than in the low bit (con-leche's lesson 6,
`_tmp/t97/conleche-arena-history.md` §6.6) — a persistent handle's bits never
change when the scratch tier comes and goes.

Four handle kinds share one implementation through a phantom type parameter,
which is nanoda's `Ptr<A>` (`util.rs:35-46`, `_tmp/t97/nanoda-design.md` §1)
with `PhantomData<A>` spelled as an index: `Idx k` is a one-field structure
over `UInt32`, so the kind is erased at runtime and the four types stay
distinct to the elaborator.

The word IS the hash (nanoda's `UniqueHasher`, `unique_hasher.rs`): every
handle-keyed table buckets on the raw word with no mixing.

## Arithmetic, not bit operations — and why

DESIGN §8.4 lesson 7 asks for `>>>`/`&&&`/`|||`.  This module uses `*`, `/`
and `%` by powers of two instead, which is con-leche's own ruling for exactly
this problem (`ConLeche/Kernel/Expr.lean:168-172`, task #167):

> The packing is written with **arithmetic**, not bitwise, operators (`*
> 65536` for a shift, `/ 65536 % 32768` for a field read): the code LLVM
> emits is the same shift-and-mask, and every roundtrip lemma below is then
> `omega` after `UInt64.toNat`.

The measured reason to prefer it here is stronger than codegen: the bitwise
form's roundtrip lemmas are not `omega`-provable and need `bv_decide`, and
`bv_decide` **introduces an axiom** (`…_native.bv_decide.ax_…`, visible at
`#print axioms`) — a new entry in the trust surface (OVERVIEW §8, task #95)
for a fact `omega` proves outright.  Lesson 7's codegen concern (`2 * p` is
`lean_nat_mul` with an overflow check) is about `Nat`; `UInt32.mul`/`div`
are machine ops with a constant operand.
-/
import Std.Data.HashMap

namespace ConRon.Arena

/-- con-leche: none — the phantom kind of a handle; nanoda's `Ptr<A>` type
argument (`util.rs:82-88`), which a Lean port cannot spell as a lifetime. -/
inductive IdxKind where
  | expr
  | name
  | level
  | levels
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: none — the arena handle.  con-leche's arena era used a bare
`Nat` with a low tier bit (`Setlec/Kernel/IExpr.lean:31`, history §1.10);
this is the high-tag / identity-embedding layout DESIGN §8.3 rules for. -/
structure Idx (k : IdxKind) where
  ofWord ::
  word : UInt32
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: none — expression handle (DESIGN §8.3). -/
abbrev EIdx := Idx .expr
/-- con-leche: none — name handle (DESIGN §8.3). -/
abbrev NIdx := Idx .name
/-- con-leche: none — level handle (DESIGN §8.3). -/
abbrev LIdx := Idx .level
/-- con-leche: none — level-list handle (DESIGN §8.3). -/
abbrev LsIdx := Idx .levels

namespace Idx

variable {k : IdxKind}

/-- con-leche: none — structural equality of handles is equality of the word. -/
instance : BEq (Idx k) := ⟨fun a b => a.word == b.word⟩

/-- con-leche: none — and it is lawful, so a `Std.HashMap` keyed by a handle
behaves as a partial function on words. -/
instance : LawfulBEq (Idx k) where
  eq_of_beq := by intro a b h; cases a; cases b; simp_all [BEq.beq]
  rfl := by intro a; simp [BEq.beq]

/-- con-leche: none — **the word IS the hash**: nanoda's identity hasher
(`unique_hasher.rs`, `_tmp/t97/nanoda-design.md` §2), no mixing at all. -/
instance : Hashable (Idx k) := ⟨fun i => i.word.toUInt64⟩

/-- con-leche: none — the persistent tier's bit value (DESIGN §8.3). -/
def tierP : UInt32 := 0
/-- con-leche: none — the scratch tier's bit value (DESIGN §8.3). -/
def tierS : UInt32 := 1

/-- con-leche: none — `2^27`: the per-constructor, per-tier node capacity.
Behind a top-level `def` because a large literal inline compiles to a GMP
parse per use (DESIGN §8.4 lesson 7). -/
def idxCap : Nat := 134217728

/-- con-leche: none — assemble a handle from its three fields.  `+`, not
`|||`: the fields are disjoint, so addition *is* the bitwise join, and the
arithmetic form is what makes the roundtrip lemmas `omega`-provable
(`ConLeche/Kernel/Expr.lean:256-260 packData`). -/
@[inline] def mk (tag tier idx : UInt32) : Idx k :=
  ⟨tag * 268435456 + tier * 134217728 + idx⟩

/-- con-leche: none — the constructor tag (bits 31…28). -/
@[inline] def tag (i : Idx k) : UInt32 := i.word / 268435456

/-- con-leche: none — the tier bit (bit 27). -/
@[inline] def tier (i : Idx k) : UInt32 := i.word / 134217728 % 2

/-- con-leche: none — the index into the constructor's array (bits 26…0). -/
@[inline] def index (i : Idx k) : UInt32 := i.word % 134217728

/-- con-leche: none — is this handle in the persistent tier?  A persistent
handle survives `dropScratch`; a scratch one does not (DESIGN §8.3). -/
@[inline] def isPersistent (i : Idx k) : Bool := i.tier == 0

/-- con-leche: none — a handle's index, as the `Nat` every array read wants. -/
@[inline] def idxNat (i : Idx k) : Nat := i.index.toNat

/-! ## The layout roundtrip

Every lemma is `omega` after `UInt32.toNat`; the hypotheses are stated on
`toNat` so that a caller's `by decide` on a literal tag discharges them and
`omega` sees plain `Nat` arithmetic. -/

theorem tag_mk (t tr n : UInt32) (ht : t.toNat < 16) (htr : tr.toNat < 2)
    (hn : n.toNat < idxCap) : (mk (k := k) t tr n).tag = t := by
  rw [idxCap] at hn
  apply UInt32.toNat_inj.mp
  simp [tag, mk, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_div]
  omega

theorem tier_mk (t tr n : UInt32) (_ht : t.toNat < 16) (htr : tr.toNat < 2)
    (hn : n.toNat < idxCap) : (mk (k := k) t tr n).tier = tr := by
  rw [idxCap] at hn
  apply UInt32.toNat_inj.mp
  simp [tier, mk, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_div,
    UInt32.toNat_mod]
  omega

theorem index_mk (t tr n : UInt32) (_ht : t.toNat < 16) (_htr : tr.toNat < 2)
    (hn : n.toNat < idxCap) : (mk (k := k) t tr n).index = n := by
  rw [idxCap] at hn
  apply UInt32.toNat_inj.mp
  simp [index, mk, UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_mod]
  omega

/-- The three fields determine the word — this is what makes `denote_inj`'s
final step (two handles with the same tag, tier and index are equal) a
one-liner. -/
theorem eta (i : Idx k) : mk i.tag i.tier i.index = i := by
  cases i with | ofWord w =>
  simp only [mk, tag, tier, index, Idx.ofWord.injEq]
  apply UInt32.toNat_inj.mp
  have hw := w.toNat_lt_size
  simp only [UInt32.size] at hw
  simp [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_div, UInt32.toNat_mod]
  omega

theorem ext_of {i j : Idx k} (ht : i.tag = j.tag) (hr : i.tier = j.tier)
    (hn : i.index = j.index) : i = j := by
  rw [← eta i, ← eta j, ht, hr, hn]

theorem tag_lt (i : Idx k) : i.tag.toNat < 16 := by
  have hw := i.word.toNat_lt_size
  simp only [UInt32.size] at hw
  simp [tag, UInt32.toNat_div]
  omega

theorem tier_lt (i : Idx k) : i.tier.toNat < 2 := by
  simp [tier, UInt32.toNat_div, UInt32.toNat_mod]
  omega

theorem index_lt (i : Idx k) : i.index.toNat < idxCap := by
  rw [idxCap]
  simp [index, UInt32.toNat_mod]
  omega

theorem idxNat_lt (i : Idx k) : i.idxNat < idxCap := index_lt i

theorem idxNat_mk (t tr : UInt32) (n : Nat) (ht : t.toNat < 16)
    (htr : tr.toNat < 2) (hn : n < idxCap) :
    (mk (k := k) t tr (UInt32.ofNat n)).idxNat = n := by
  have hn' : n < 134217728 := by rw [idxCap] at hn; exact hn
  have h : (UInt32.ofNat n).toNat < idxCap := by
    rw [idxCap]; simp; omega
  rw [idxNat, index_mk t tr _ ht htr h]
  simp; omega

/-- A scratch handle and a persistent handle are never equal — the tier bit
separates them, which is what makes `dropScratch` sound (DESIGN §8.3). -/
theorem ne_of_tier_ne {i j : Idx k} (h : i.tier ≠ j.tier) : i ≠ j := by
  intro he; exact h (by rw [he])

end Idx

/-! ## The constructor tags

One namespace per store, values fixed by con-leche's own constructor order so
that a reader can line the two up by eye.

con-leche: ConLeche/Kernel/Expr.lean:344-353 Expr — the ten expression
constructor tags, in con-leche's declaration order. -/
namespace ETag
def bvar : UInt32 := 0
def fvar : UInt32 := 1
def sort : UInt32 := 2
def const : UInt32 := 3
def app : UInt32 := 4
def lam : UInt32 := 5
def forallE : UInt32 := 6
def letE : UInt32 := 7
def lit : UInt32 := 8
def proj : UInt32 := 9
end ETag

/-! con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the three name
constructor tags. -/
namespace NTag
def anonymous : UInt32 := 0
def str : UInt32 := 1
def num : UInt32 := 2
end NTag

/-! con-leche: ConLeche/Kernel/Expr.lean:40-45 Level — the five level
constructor tags. -/
namespace LTag
def zero : UInt32 := 0
def succ : UInt32 := 1
def max : UInt32 := 2
def imax : UInt32 := 3
def param : UInt32 := 4
end LTag

/-! con-leche: none — level *lists* are interned as one object (nanoda's
`LevelsPtr`, `_tmp/t97/nanoda-design.md` §1), so the store has a single
constructor and a single tag. -/
namespace LsTag
def list : UInt32 := 0
end LsTag

end ConRon.Arena
