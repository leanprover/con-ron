/-
# `ConRon.Bridge.Core.Walks.Frame` — the frame every non-slot walk needs

Task #97-P3-CoreWalks.  DESIGN §8's `### Task #97-P3-Core` §6 names what the
six body walks are waiting on: *"a `BodySpec`-shaped theorem for the
`Arena/Core.lean` walks that are not knot slots"*.  This module is that
tier's foundation — the one fact all of them share, and the item task
#97-P3-0's own §7 lists as owed ("the per-call memo FRAME").

## The problem, concretely

`CheckOK` (`Bridge/StateOK.lean`) carries the invariant of **all fourteen**
per-declaration cache tables, and *most* of the non-slot walks of
`Arena/Core.lean` read a name, a level or a universe-argument list back.
`Bridge/Specs.lean`'s three readback specs used to conclude
`s'.store = s₀.store ∧ s'.memos = s₀.memos ∧ s'.pins = s₀.pins` plus their
own table's invariant and **nothing about the other thirteen tables**, so no
such walk could rebuild `CheckOK` at all.

`ReadbackFrame` below is the fact that was missing, and it is ONE equation
rather than fourteen: *the cache record after the call is the cache record before
it with the three readback tables replaced*.  From that, `rw` recovers each
of the eleven clauses that did not move; the three that did are carried as
implications in the same structure, which is what makes `.trans` compose.

## Where the equation lives, and the detour that is no longer needed

The equation is a conjunct of `Bridge/Specs.lean`'s three readback specs.
It was NOT there when this module was first written, and the round's first
shape worked round the gap with a body copy per readback
(`readLevelMB`, `readNameMB`, `readLevelsMB`, each `= rfl` to the real
function and each with no spec of its own) plus a
`simp only [<the walk>, readLevelM_eq, …]` line in front of every walk's
`mvcgen` — because `mvcgen` prefers a registered `@[spec]` theorem to
unfolding the definition, and **`attribute [-spec]` is not available**
(`[spec]` cannot be erased), so the frame could be proved neither *from* the
weaker spec nor by unfolding past it.

Strengthening the three specs is a ONE-CONJUNCT edit that costs their proofs
one `rfl` each, and it deletes the three copies, the three `= rfl` bridges,
the three body-level frame theorems and the `simp only` line from every walk
of the tier.  `ReadbackFrame.ofReadL` / `.ofReadN` / `.ofReadLs` below are
what is left: one constructor per readback, taking the spec's own conjuncts.
-/
import ConRon.Bridge.Core.Memo

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ## 1. The frame -/

/-- con-leche: none — **the readback frame**: the call moved the three
readback memos and nothing else, and it kept their invariants.

The fourth field is the content; the first three are what
`Bridge/Specs.lean` already says and are repeated so that `.trans` needs one
hypothesis rather than four.  The last three are *implications* rather than
facts, so that `.refl` is `id` and the structure composes without carrying
the invariant as a side condition. -/
structure ReadbackFrame (s₀ s' : AState) : Prop where
  store : s'.store = s₀.store
  memos : s'.memos = s₀.memos
  pins : s'.pins = s₀.pins
  caches : s'.caches = { s₀.caches with
    readLC := s'.caches.readLC, readNC := s'.caches.readNC,
    readLsC := s'.caches.readLsC }
  readL : ReadLCacheOK s₀.caches.readLC s₀.store →
    ReadLCacheOK s'.caches.readLC s'.store
  readN : ReadNCacheOK s₀.caches.readNC s₀.store →
    ReadNCacheOK s'.caches.readNC s'.store
  readLs : ReadLsCacheOK s₀.caches.readLsC s₀.store →
    ReadLsCacheOK s'.caches.readLsC s'.store

/-- con-leche: none — the identity frame. -/
theorem ReadbackFrame.refl (s : AState) : ReadbackFrame s s :=
  ⟨rfl, rfl, rfl, rfl, id, id, id⟩

/-- con-leche: none — frames compose, which is what lets a walk that reads
several handles back pay the obligation once. -/
theorem ReadbackFrame.trans {s₀ s₁ s₂ : AState} (h : ReadbackFrame s₀ s₁)
    (h' : ReadbackFrame s₁ s₂) : ReadbackFrame s₀ s₂ where
  store := h'.store.trans h.store
  memos := h'.memos.trans h.memos
  pins := h'.pins.trans h.pins
  caches := by rw [h'.caches, h.caches]
  readL := fun x => h'.readL (h.readL x)
  readN := fun x => h'.readN (h.readN x)
  readLs := fun x => h'.readLs (h.readLs x)

/-- con-leche: none — a frame is in particular an arena extension, which is
what a caller stating `Ext` in its own postcondition needs. -/
theorem ReadbackFrame.ext {s₀ s' : AState} (h : ReadbackFrame s₀ s') :
    Ext s₀.store s'.store := by rw [h.store]; exact Ext.refl _

/-! ## 2. `CacheOK` and `CheckOK` across a frame -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC (the
frame half) — **the eleven clauses that did not move**, recovered from the
one equation, plus the three that did, carried by the frame itself. -/
theorem CacheOK.ofReadbackFrame {mode : CheckMode} {env : Env} {s s' : AState}
    (h : CacheOK mode env s) (hf : ReadbackFrame s s') : CacheOK mode env s'
    where
  whnfCore := by rw [hf.caches, hf.store]; exact h.whnfCore
  whnf := by rw [hf.caches, hf.store]; exact h.whnf
  infer := by rw [hf.caches, hf.store]; exact h.infer
  inferIO := by rw [hf.caches, hf.store]; exact h.inferIO
  annot := by rw [hf.caches, hf.store]; exact h.annot
  defeq := by rw [hf.caches, hf.store]; exact h.defeq
  lvlEq := by rw [hf.caches, hf.store]; exact h.lvlEq
  lvlsEq := by rw [hf.caches, hf.store]; exact h.lvlsEq
  constTy := by rw [hf.caches, hf.store]; exact h.constTy
  constVal := by rw [hf.caches, hf.store]; exact h.constVal
  ruleRhs := by rw [hf.caches, hf.store]; exact h.ruleRhs
  readL := hf.readL h.readL
  readN := hf.readN h.readN
  readLs := hf.readLs h.readLs

/-- con-leche: none — **`CheckOK` across a readback frame**: the store, the
pins and the environment index did not move, so only the cache clause has
content.  This is the theorem every non-slot walk of the tier ends on. -/
theorem CheckOK.ofReadbackFrame {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK mode env fe s) (hf : ReadbackFrame s s') :
    CheckOK mode env fe s' :=
  CheckOK.ofCache h (CacheOK.ofReadbackFrame h.caches hf) hf.store hf.pins

/-! ## 3. The frame from `Bridge/Specs.lean`'s three readback specs

One constructor per readback.  Each takes the spec's four frame conjuncts and
its table's invariant and builds the `ReadbackFrame`; the two tables the call
did not touch come out of the `caches` equation by projection. -/

/-- con-leche: none — the frame of a `readLevelM` call. -/
theorem ReadbackFrame.ofReadL {s0 s1 : AState}
    (hst : s1.store = s0.store) (hm : s1.memos = s0.memos)
    (hp : s1.pins = s0.pins)
    (hc : s1.caches = { s0.caches with readLC := s1.caches.readLC })
    (hL : ReadLCacheOK s1.caches.readLC s1.store) : ReadbackFrame s0 s1 where
  store := hst
  memos := hm
  pins := hp
  caches := by
    have hN : s1.caches.readNC = s0.caches.readNC := by rw [hc]
    have hLs : s1.caches.readLsC = s0.caches.readLsC := by rw [hc]
    rw [hN, hLs]; exact hc
  readL := fun _ => hL
  readN := fun hn => by
    have hN : s1.caches.readNC = s0.caches.readNC := by rw [hc]
    rw [hN, hst]; exact hn
  readLs := fun hn => by
    have hLs : s1.caches.readLsC = s0.caches.readLsC := by rw [hc]
    rw [hLs, hst]; exact hn

/-- con-leche: none — the frame of a `readNameM` call. -/
theorem ReadbackFrame.ofReadN {s0 s1 : AState}
    (hst : s1.store = s0.store) (hm : s1.memos = s0.memos)
    (hp : s1.pins = s0.pins)
    (hc : s1.caches = { s0.caches with readNC := s1.caches.readNC })
    (hN : ReadNCacheOK s1.caches.readNC s1.store) : ReadbackFrame s0 s1 where
  store := hst
  memos := hm
  pins := hp
  caches := by
    have hL : s1.caches.readLC = s0.caches.readLC := by rw [hc]
    have hLs : s1.caches.readLsC = s0.caches.readLsC := by rw [hc]
    rw [hL, hLs]; exact hc
  readL := fun hl => by
    have hL : s1.caches.readLC = s0.caches.readLC := by rw [hc]
    rw [hL, hst]; exact hl
  readN := fun _ => hN
  readLs := fun hn => by
    have hLs : s1.caches.readLsC = s0.caches.readLsC := by rw [hc]
    rw [hLs, hst]; exact hn

/-- con-leche: none — the frame of a `readLevelsM` call. -/
theorem ReadbackFrame.ofReadLs {s0 s1 : AState}
    (hst : s1.store = s0.store) (hm : s1.memos = s0.memos)
    (hp : s1.pins = s0.pins)
    (hc : s1.caches = { s0.caches with readLsC := s1.caches.readLsC })
    (hLs : ReadLsCacheOK s1.caches.readLsC s1.store) : ReadbackFrame s0 s1
    where
  store := hst
  memos := hm
  pins := hp
  caches := by
    have hL : s1.caches.readLC = s0.caches.readLC := by rw [hc]
    have hN : s1.caches.readNC = s0.caches.readNC := by rw [hc]
    rw [hL, hN]; exact hc
  readL := fun hl => by
    have hL : s1.caches.readLC = s0.caches.readLC := by rw [hc]
    rw [hL, hst]; exact hl
  readN := fun hn => by
    have hN : s1.caches.readNC = s0.caches.readNC := by rw [hc]
    rw [hN, hst]; exact hn
  readLs := fun _ => hLs

end ConRon.Bridge.Core
