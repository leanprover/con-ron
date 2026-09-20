/-
# `ConRon.Arena.CoreState` — the checker-level caches of (B)

DESIGN.md §8.3, "Caches", second and third bullets.  `Arena/Monad.lean`'s
`Memos` holds the **per-call** tables of the `ExprOps` twins — cleared at
every top-level entry, because their answers depend on the substituted term.
This module holds the **per-declaration** ones, which the checker keeps for
the whole of one declaration's check and drops at its boundary:

* the five unary entry-point memos `whnfCore`, `whnf`, `infer`, `inferIO`,
  `annotate` : `EIdx ↦ EIdx` — *three separate infer grades*, because
  con-leche's lesson 9 is that a hit in one grade must never serve another
  (`ConLeche/Cached/CoreC.lean:1966-1975`: "a hit in the io memo never
  serves a full-infer query");
* `defeq` on the ORDERED pair with the `Bool` verdict, both signs — the
  shape con-leche's arena stored (`defeqC`, `Cached/CoreC.lean:1893-1906`),
  which is what makes a negative memo sound: the pure run at the fixed fuel
  answered `r`, and the memo answers `r`;
* the two level-verdict caches (`(LIdx × LIdx)`, `(LsIdx × LsIdx)`), DESIGN
  §8.3 "Levels and names": the ALGORITHM runs on transient trees, the
  VERDICT is cached on the handles;
* the lazy instantiated-constant caches (`constTyAt` / `constValAt` /
  `ruleRhsAt`, con-leche's arena task #26), keyed on the name and the
  universe-argument list rather than on the instantiated term — every
  `cv.type.instantiateLevelParams cv.levelParams us` in the checker is one
  of these three.

**A cap, not an eviction policy** (DESIGN §8.3, lesson 10): past
`cacheCap` entries a table is dropped whole and starts again.  No LRU, no
per-entry bookkeeping, and the Rust is one `len()` test.

**`dropScratchEntries`** is the per-declaration bracket's other half: an
entry whose key or value names a SCRATCH handle must not survive the tier
that owns it (the handle is about to be reused by the next declaration),
while an entry that is persistent through and through may (con-leche's
arena #51).  The test is the tier bit, `Idx.isPersistent` — no allocation,
no denotation.

This module imports `Arena/Handle.lean` and NOTHING else, so that
`Arena/Monad.lean` can put a `Caches` into `AState` without a cycle: the
record is data over handles, and every operation on it that needs the
monad lives in `Arena/Core.lean` beside the knot that probes it.
-/
import ConRon.Arena.Handle

namespace ConRon.Arena

/-! ## The record -/

/-- con-leche: ConLeche/Cached/StateC.lean:127-156 CState — the
per-declaration caches of the arena checker, in one record beside
`Monad.lean`'s per-call `Memos`.  Keeping the two apart is deliberate: the
per-call clear (`inst1Clear` and its ten siblings) and the per-declaration
drop (`dropScratchEntries`) are different operations on different
lifetimes, and a frame condition about either is one equation. -/
structure Caches where
  /-- `whnfCore` at the node (con-leche `CState.whnfCoreC`).  The depth is
  NOT in the key: a handle carries its own typing context, because an
  `fvar` node carries its type (DESIGN §8.3, "Free variables"). -/
  whnfCoreC : Std.HashMap EIdx EIdx
  /-- The full reduction loop at the node (`CState.whnfC`). -/
  whnfC : Std.HashMap EIdx EIdx
  /-- Full-grade inference (`CState.inferC`). -/
  inferC : Std.HashMap EIdx EIdx
  /-- **The io grade's own table** (`CState.inferIOC`): a hit here never
  serves a full-`infer` query, and a full-`infer` hit never serves this
  one. -/
  inferIOC : Std.HashMap EIdx EIdx
  /-- The annotation pass at the node (`CState.annotC`). -/
  annotC : Std.HashMap EIdx EIdx
  /-- Definitional equality at the ORDERED pair, with the verdict — both
  signs, as con-leche's `defeqC` stores them. -/
  defeqC : Std.HashMap (EIdx × EIdx) Bool
  /-- `Level.isEquiv`'s verdict at a pair of level handles. -/
  lvlEqC : Std.HashMap (LIdx × LIdx) Bool
  /-- `Level.isEquivList`'s verdict at a pair of universe-argument lists. -/
  lvlsEqC : Std.HashMap (LsIdx × LsIdx) Bool
  /-- A stored constant's TYPE at a universe instantiation. -/
  constTyC : Std.HashMap (NIdx × LsIdx) EIdx
  /-- A stored definition's VALUE at a universe instantiation. -/
  constValC : Std.HashMap (NIdx × LsIdx) EIdx
  /-- An iota rule's right-hand side at the recursor's universe
  instantiation, keyed by the recursor, the rule's constructor and the
  levels — the three data that determine it. -/
  ruleRhsC : Std.HashMap (NIdx × NIdx × LsIdx) EIdx

/-- con-leche: ConLeche/Cached/StateC.lean:131-156 CState — the empty
cache set: what a fresh run and every capped table start from. -/
def Caches.empty : Caches := ⟨∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅⟩

instance : Inhabited Caches := ⟨Caches.empty⟩

/-! ## The cap -/

/-- con-leche: none — DESIGN §8.3's cap (lesson 10, "a cap, not an eviction
policy"): a table that reaches this many entries is dropped whole.  A
top-level `def` so the Rust is a `const` and the Lean never inlines a
`Nat` literal into a comparison (DESIGN §8.4, lesson 7). -/
def cacheCap : Nat := 4194304

/-! ## The scratch-tier drop -/

/-- con-leche: none — DESIGN §8.3, "Drop": a memo entry survives the
scratch tier exactly when BOTH its key and its value are persistent
handles.  One tier-bit test each, no denotation. -/
@[inline] def keepE (k : EIdx) (v : EIdx) : Bool :=
  k.isPersistent && v.isPersistent

/-- con-leche: none — the `defeq` table's survival test: both handles of
the key are persistent (the value is a `Bool` and names no tier). -/
@[inline] def keepEE (k : EIdx × EIdx) (_v : Bool) : Bool :=
  k.1.isPersistent && k.2.isPersistent

/-- con-leche: none — the level-verdict tables' survival test. -/
@[inline] def keepLL (k : LIdx × LIdx) (_v : Bool) : Bool :=
  k.1.isPersistent && k.2.isPersistent

/-- con-leche: none — the level-list-verdict table's survival test. -/
@[inline] def keepLsLs (k : LsIdx × LsIdx) (_v : Bool) : Bool :=
  k.1.isPersistent && k.2.isPersistent

/-- con-leche: none — the instantiated-constant tables' survival test:
the name, the universe-argument list and the instantiated term. -/
@[inline] def keepNLs (k : NIdx × LsIdx) (v : EIdx) : Bool :=
  k.1.isPersistent && k.2.isPersistent && v.isPersistent

/-- con-leche: none — `ruleRhsC`'s survival test. -/
@[inline] def keepNNLs (k : NIdx × NIdx × LsIdx) (v : EIdx) : Bool :=
  k.1.isPersistent && k.2.1.isPersistent && k.2.2.isPersistent &&
    v.isPersistent

/-- con-leche: none — **the per-declaration bracket's cache half**
(DESIGN §8.3, "Drop"), kept as the *specification* of what a surviving row
is: an entry whose key or value names a scratch handle must go with the tier
that owns the handle, and an entry that is persistent through and through
may stay.  Nothing calls it (see `Caches.flushed` below, and task #97f).

The Rust spelling would be `HashMap::retain` per table; the Lean is
`Std.HashMap.filter`, whose predicate is one of the six named tests above
rather than a lambda (DESIGN §3.4: no closures in code Aeneas must
translate). -/
def Caches.dropScratchEntries (c : Caches) : Caches :=
  { whnfCoreC := c.whnfCoreC.filter keepE
    whnfC := c.whnfC.filter keepE
    inferC := c.inferC.filter keepE
    inferIOC := c.inferIOC.filter keepE
    annotC := c.annotC.filter keepE
    defeqC := c.defeqC.filter keepEE
    lvlEqC := c.lvlEqC.filter keepLL
    lvlsEqC := c.lvlsEqC.filter keepLsLs
    constTyC := c.constTyC.filter keepNLs
    constValC := c.constValC.filter keepNLs
    ruleRhsC := c.ruleRhsC.filter keepNNLs }

/-- con-leche: ConLeche/Cached/StateC.lean:394-398 CState.flushed — **what the
per-declaration bracket actually does to the caches**: it drops them whole,
which is con-leche's own `flushC`, the operation its driver runs at exactly
this point (`Cached/Installed.lean`'s phase B runs every pending check from
`{}`).

Task #97c took DESIGN §8.3's survivor policy instead — keep the rows whose key
AND value are persistent — which is sound (a dropped row is a cache miss and
nothing else) and strictly more caching.  Task #97f measured what it costs: a
`filter` is `O(table)` and the survivors accumulate, so the fold pays
`O(declarations × surviving rows)`.  On the first 4 380 declarations of `Init`
the filter and its bucket-array rebuild were **16 % of the cycles** directly,
and with the allocation traffic they drove the flush takes the same prefix
from **213 s to 124 s**.  DESIGN §8.3's "Drop" clause is amended to say so.
(It is not the whole story: that prefix is still superlinear in the
declaration count, which is P6's.)

`dropScratchEntries` stays above as the specification of a surviving row —
P3 needs it to state that flushing is sound, since `flushed ⊑ dropScratchEntries`
as caches. -/
def Caches.flushed (_c : Caches) : Caches := Caches.empty

end ConRon.Arena
