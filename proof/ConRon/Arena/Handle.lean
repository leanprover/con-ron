/-
# The arena's handles (DESIGN.md §8.3, task #97 P2a)

One 32-bit word per handle, in one of two shapes.  The top bit is the tier in
both; bit 30 says which shape the rest is:

    wide   (expression `app` only)        narrow (every other node)
    bit  31      tier                     bit  31      tier
    bit  30      1                        bit  30      0
    bits 29…0    index                    bits 29…26   ctor tag   (4 bits)
                                          bits 25…0    index

(tier 0 = persistent, 1 = scratch; the index is into THAT CONSTRUCTOR'S array
of THAT TIER).  So the zero word is a narrow handle — tag 0, persistent,
slot 0, the first node of every store's tag-0 array (the anonymous name, the
level `zero`) — which is what makes `default : Idx k` a handle that decodes.
An expression `app` array holds 2^30 nodes per tier and
every other constructor array 2^26: apps are 85 % of an export's expression
nodes, so they are the array that runs out first, and they get the room.
Only the expression `app` tag is wide — a level `param` handle is narrow
although `LTag.param` has `ETag.app`'s value — and `tag` reads `ETag.app` off
a word with bit 30 set, so a handle's tag is read the same way at all four
kinds.  The tier is the TOP bit, above both shapes' index, so — con-leche's
lesson 6, `_tmp/t97/conleche-arena-history.md` §6.6 — a persistent handle's
bits never change when the scratch tier comes and goes.

The decode `(tag, tier, index)` is not injective on ALL words: a narrow word
with tag field 4 reads like the wide word with its index.  No store makes
such a handle at the kind where it would collide (only `mkWide` makes an
expression `app`, only `mk` a level `param`), and the two `get`s that could
see one (`ETables.get`'s `app` arm, `LTables.get`'s `param` arm) test
`isWide`, so `view` stays injective; `ext_of` takes the shape as a fourth
field for the same reason.

Five handle kinds share one implementation through a phantom type parameter,
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

The measured reason to prefer it here is stronger than codegen: every
roundtrip lemma below is one `grind` call over `UInt32` directly (its linear
arithmetic handles `/` and `%` by a literal), while the bitwise form's would
need `bv_decide`, and `bv_decide` **introduces an axiom**
(`…_native.bv_decide.ax_…`, visible at `#print axioms`) — a new entry in the
trust surface (OVERVIEW §8, task #95) for a fact linear arithmetic proves
outright.  Lesson 7's codegen concern (`2 * p` is
`lean_nat_mul` with an overflow check) is about `Nat`; `UInt32.mul`/`div`
are machine ops with a constant operand.
-/
module

public import Std.Data.HashMap

@[expose] public section

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

/-- con-leche: none — `2^26`: the per-constructor, per-tier node capacity of
every constructor but the expression `app` (a narrow handle's index field).
Behind a top-level `def` because a large literal inline compiles to a GMP
parse per use (DESIGN §8.4 lesson 7). -/
def idxCap : Nat := 67108864

/-- con-leche: none — `2^30`: the expression `app` array's per-tier capacity
(a wide handle's index field). -/
def wideCap : Nat := 1073741824

/-- con-leche: none — assemble a NARROW handle from its three fields: the tier
on top, bit 30 clear, the tag in bits 29…26, the index below.  `+`, not `|||`:
the fields are disjoint, so addition *is* the bitwise join, and the
arithmetic form is what makes the roundtrip lemmas `grind`-provable
(`ConLeche/Kernel/Expr.lean:256-260 packData`). -/
@[inline] def mk (tag tier idx : UInt32) : Idx k :=
  ⟨tier * 2147483648 + tag * 67108864 + idx⟩

/-- con-leche: none — assemble a WIDE handle, an expression `app`'s: the tier
on top, bit 30 set, the index in bits 29…0. -/
@[inline] def mkWide (tier idx : UInt32) : Idx k :=
  ⟨tier * 2147483648 + 1073741824 + idx⟩

/-- con-leche: none — is this a wide word (bit 30 set), i.e. an expression
`app` handle? -/
@[inline] def isWide (i : Idx k) : Bool := i.word / 1073741824 % 2 == 1

/-- con-leche: none — the constructor tag: `ETag.app` (4) for a wide word,
bits 29…26 of a narrow one. -/
@[inline] def tag (i : Idx k) : UInt32 :=
  if i.isWide then 4 else i.word / 67108864 % 16

/-- con-leche: none — the tier bit (bit 31). -/
@[inline] def tier (i : Idx k) : UInt32 := i.word / 2147483648

/-- con-leche: none — the index into the constructor's array: bits 29…0 of a
wide word, bits 25…0 of a narrow one. -/
@[inline] def index (i : Idx k) : UInt32 :=
  if i.isWide then i.word % 1073741824 else i.word % 67108864

/-- con-leche: none — is this handle in the persistent tier?  A persistent
handle survives `dropScratch`; a scratch one does not (DESIGN §8.3). -/
@[inline] def isPersistent (i : Idx k) : Bool := i.tier == 0

/-- con-leche: none — a handle's index, as the `Nat` every array read wants. -/
@[inline] def idxNat (i : Idx k) : Nat := i.index.toNat

/-! ## The layout roundtrip

Every lemma is one `grind` over `UInt32` (its linear arithmetic handles `/`
and `%` by a literal); the hypotheses are stated on `toNat` so that a
caller's `by decide` on a literal tag discharges them. -/

theorem isWide_mk (t tr n : UInt32) (ht : t.toNat < 16) (_htr : tr.toNat < 2)
    (hn : n.toNat < idxCap) : (mk (k := k) t tr n).isWide = false := by
  grind [isWide, mk, idxCap]

theorem tag_mk (t tr n : UInt32) (ht : t.toNat < 16) (_htr : tr.toNat < 2)
    (hn : n.toNat < idxCap) : (mk (k := k) t tr n).tag = t := by
  grind [tag, isWide, mk, idxCap]

theorem tier_mk (t tr n : UInt32) (ht : t.toNat < 16) (htr : tr.toNat < 2)
    (hn : n.toNat < idxCap) : (mk (k := k) t tr n).tier = tr := by
  grind [tier, mk, idxCap]

theorem index_mk (t tr n : UInt32) (ht : t.toNat < 16) (_htr : tr.toNat < 2)
    (hn : n.toNat < idxCap) : (mk (k := k) t tr n).index = n := by
  grind [index, isWide, mk, idxCap]

theorem index_mkWide (tr n : UInt32) (_htr : tr.toNat < 2)
    (hn : n.toNat < wideCap) : (mkWide (k := k) tr n).index = n := by
  grind [index, isWide, mkWide, wideCap]

/-- The fields determine the word — the shape, then the tag (narrow only),
tier and index.  This is what makes `denote_inj`'s final step (two handles
with the same fields are equal) a one-liner. -/
theorem eta (i : Idx k) :
    (if i.isWide then mkWide i.tier i.index else mk i.tag i.tier i.index) = i := by
  cases i with | ofWord w =>
  simp only [mkWide, mk]
  grind [index, isWide, tier, tag]

theorem ext_of {i j : Idx k} (hw : i.isWide = j.isWide) (ht : i.tag = j.tag)
    (hr : i.tier = j.tier) (hn : i.index = j.index) : i = j := by
  rw [← eta i, ← eta j, hw, ht, hr, hn]

theorem tier_lt (i : Idx k) : i.tier.toNat < 2 := by
  grind [tier]

theorem idxNat_mk (t tr : UInt32) (n : Nat) (ht : t.toNat < 16)
    (htr : tr.toNat < 2) (hn : n < idxCap) :
    (mk (k := k) t tr (UInt32.ofNat n)).idxNat = n := by
  have h : (UInt32.ofNat n).toNat = n := by grind [idxCap]
  rw [idxNat, index_mk t tr _ ht htr (by rw [h]; exact hn), h]

theorem idxNat_mkWide (tr : UInt32) (n : Nat) (htr : tr.toNat < 2)
    (hn : n < wideCap) :
    (mkWide (k := k) tr (UInt32.ofNat n)).idxNat = n := by
  have h : (UInt32.ofNat n).toNat = n := by grind [wideCap]
  rw [idxNat, index_mkWide tr _ htr (by rw [h]; exact hn), h]

/-! The same fields at a `Nat` index, the shape every `push` builds
(`UInt32.ofNat tb.size`). -/

theorem isWide_mk_ofNat (t tr : UInt32) (n : Nat) (ht : t.toNat < 16)
    (hn : n < idxCap) : (mk (k := k) t tr (UInt32.ofNat n)).isWide = false := by
  grind [isWide, mk, idxCap]

theorem tag_mk_ofNat (t tr : UInt32) (n : Nat) (ht : t.toNat < 16)
    (hn : n < idxCap) : (mk (k := k) t tr (UInt32.ofNat n)).tag = t := by
  grind [tag, isWide, mk, idxCap]

theorem isWide_mkWide_ofNat (tr : UInt32) (n : Nat) (hn : n < wideCap) :
    (mkWide (k := k) tr (UInt32.ofNat n)).isWide = true := by
  grind [isWide, mkWide, wideCap]

theorem tag_mkWide_ofNat (tr : UInt32) (n : Nat) (hn : n < wideCap) :
    (mkWide (k := k) tr (UInt32.ofNat n)).tag = 4 := by
  grind [tag, isWide, mkWide, wideCap]

theorem tier_mkWide_ofNat (tr : UInt32) (n : Nat) (htr : tr.toNat < 2)
    (hn : n < wideCap) : (mkWide (k := k) tr (UInt32.ofNat n)).tier = tr := by
  grind [tier, mkWide, wideCap]

/-- A wide handle reads the `app` tag; so a handle whose tag is not 4 is
narrow. -/
theorem tag_of_isWide {i : Idx k} (h : i.isWide = true) : i.tag = 4 := by
  simp [tag, h]

theorem isWide_eq_false_of_tag_ne {i : Idx k} (h : i.tag ≠ 4) : i.isWide = false := by
  cases hw : i.isWide
  · rfl
  · exact absurd (tag_of_isWide hw) h

end Idx

/-! ## The constructor tags

One namespace per store, values fixed by con-leche's own constructor order so
that a reader can line the two up by eye.  Each tag cites the parent
inductive and names the constructor it stands for. -/

namespace ETag
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `bvar`
constructor, line 316. -/
def bvar : UInt32 := 0
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `fvar`
constructor, line 317. -/
def fvar : UInt32 := 1
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `sort`
constructor, line 318. -/
def sort : UInt32 := 2
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `const`
constructor, line 319. -/
def const : UInt32 := 3
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `app`
constructor, line 320. -/
def app : UInt32 := 4
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `lam`
constructor, line 321. -/
def lam : UInt32 := 5
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `forallE`
constructor, line 322. -/
def forallE : UInt32 := 6
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `letE`
constructor, line 323. -/
def letE : UInt32 := 7
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `lit`
constructor, line 324. -/
def lit : UInt32 := 8
/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — the `proj`
constructor, line 325. -/
def proj : UInt32 := 9

/-- con-leche: ConLeche/Kernel/Expr.lean:341-460 Expr — `lam` (line 406) or
`forallE` (line 407), the two constructors that share the `BindNode` record
shape (task #97-P6-10).  A named predicate rather than the disjunction written
at the use site: the walks that dispatch on the handle's own tag hold the
handle while they test it, and task #97-P4a's extraction rule 2 asks for the
name so that a two-way `||` never sits inside a `match` arm that still holds
loans. -/
@[inline] def isBind (t : UInt32) : Bool := t == lam || t == forallE
end ETag

/-! The three name-constructor tags. -/
namespace NTag
/-- con-leche: ConLeche/Kernel/Name.lean:28-31 Name — the `anonymous`
constructor, line 28. -/
def anonymous : UInt32 := 0
/-- con-leche: ConLeche/Kernel/Name.lean:28-31 Name — the `str`
constructor, line 29. -/
def str : UInt32 := 1
/-- con-leche: ConLeche/Kernel/Name.lean:28-31 Name — the `num`
constructor, line 30. -/
def num : UInt32 := 2
end NTag

/-! The five level-constructor tags. -/
namespace LTag
/-- con-leche: ConLeche/Kernel/Expr.lean:38-43 Level — the `zero`
constructor, line 39. -/
def zero : UInt32 := 0
/-- con-leche: ConLeche/Kernel/Expr.lean:38-43 Level — the `succ`
constructor, line 40. -/
def succ : UInt32 := 1
/-- con-leche: ConLeche/Kernel/Expr.lean:38-43 Level — the `max`
constructor, line 41. -/
def max : UInt32 := 2
/-- con-leche: ConLeche/Kernel/Expr.lean:38-43 Level — the `imax`
constructor, line 42. -/
def imax : UInt32 := 3
/-- con-leche: ConLeche/Kernel/Expr.lean:38-43 Level — the `param`
constructor, line 43. -/
def param : UInt32 := 4
end LTag

/-! The level-list store's single tag. -/
namespace LsTag
/-- con-leche: none — arena infrastructure: level *lists* are interned as
one object (nanoda's `LevelsPtr`, `_tmp/t97/nanoda-design.md` §1), so the
store has a single constructor and a single tag. -/
def list : UInt32 := 0
end LsTag

end ConRon.Arena
