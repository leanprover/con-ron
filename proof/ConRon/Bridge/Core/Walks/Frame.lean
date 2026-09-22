/-
# `ConRon.Bridge.Core.Walks.Frame` — the frame every non-slot walk needs

Task #97-P3-CoreWalks.  DESIGN §8's `### Task #97-P3-Core` §6 names what the
six body walks are waiting on: *"a `BodySpec`-shaped theorem for the
`Arena/Core.lean` walks that are not knot slots"*.  This module is that
tier's foundation — the one fact all of them share, and the item task
#97-P3-0's own §7 lists as owed ("the per-call memo FRAME").

## The problem, concretely

`Bridge/Specs.lean`'s three readback specs (`readLevelM_spec`,
`readNameM_spec`, `readLevelsM_spec`) conclude `s'.store = s₀.store ∧
s'.memos = s₀.memos ∧ s'.pins = s₀.pins` and give back the readback table's
own invariant — but they say **nothing about the other thirteen cache
tables**, and `CheckOK` needs all fourteen.  So no walk that reads a name, a
level or a universe-argument list back can rebuild `CheckOK` from the spec
layer as it stands, and *most* of the non-slot walks of `Arena/Core.lean`
read one of the three.

`ReadbackFrame` below is the missing fact, and it is ONE equation rather
than fourteen: *the cache record after the call is the cache record before
it with the three readback tables replaced*.  From that, `rw` recovers each
of the eleven clauses that did not move; the three that did are carried as
implications in the same structure, which is what makes `.trans` compose.

## The `@[spec]` obstacle, and the shape that gets round it

`mvcgen` prefers a registered `@[spec]` theorem to unfolding the definition,
so with `Bridge/Specs.lean`'s three specs in scope a frame theorem about
`readLevelM` would have to be proved from their own (weaker) conclusion —
which cannot be done, since the frame's `caches` equation is exactly what
they omit.  **`attribute [-spec]` is not available** (`[spec]` cannot be
erased), and this round does not edit `Bridge/Specs.lean` (task #97-P3-0's
rule, and task #97-P3-1 was editing it concurrently).

So the tier takes the other road: **a body copy per readback**
(`readLevelMB`, `readNameMB`, `readLevelsMB`), each equal to the real
function by `rfl`, each with no spec of its own, and each with the frame
proved over its own branches.  A walk's proof then opens with

```lean
simp only [<the walk>, readLevelM_eq, readNameM_eq, readLevelsM_eq]
mvcgen [readLevelMB_frame, …]
```

— the `simp only` unfolds the walk and rewrites its readbacks to the copies
in one step, after which `mvcgen` has no registered spec to prefer.  It costs
one line per walk and scales to all of them, which a body copy per WALK would
not.  If `Bridge/Specs.lean`'s three specs are ever strengthened with the
`caches` equation, the three copies and this note go away and nothing else
in the tier changes.
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

/-! ## 3. The three readback bodies, copied

Each is `Arena/Monad.lean`'s definition verbatim, and each `…_eq` lemma is
`rfl`.  The module note says why the copies exist. -/

/-- con-leche: ConLeche/Kernel/Expr.lean:41-46 Level — `readLevelM`'s body
(`Arena/Monad.lean:535-546`), copied so that `mvcgen` sees the branches
rather than `Bridge/Specs.lean`'s spec. -/
def readLevelMB (h : LIdx) : AM Level := do
  let s ← get
  match s.caches.readLC[h]? with
  | some l => pure l
  | none =>
    match denoteL s.store.ls h with
    | none => fail (.internal "arena: dangling level handle")
    | some l =>
      let mp := s.caches.readLC
      let s := { s with caches := { s.caches with readLC := ∅ } }
      set { s with caches := { s.caches with readLC := mp.insert h l } }
      pure l

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — `readNameM`'s body
(`Arena/Monad.lean:550-561`). -/
def readNameMB (h : NIdx) : AM ConLeche.Name := do
  let s ← get
  match s.caches.readNC[h]? with
  | some x => pure x
  | none =>
    match denoteN s.store.ns h with
    | none => fail (.internal "arena: dangling name handle")
    | some x =>
      let mp := s.caches.readNC
      let s := { s with caches := { s.caches with readNC := ∅ } }
      set { s with caches := { s.caches with readNC := mp.insert h x } }
      pure x

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — `readLevelsM`'s body
(`Arena/Monad.lean:575-586`). -/
def readLevelsMB (h : LsIdx) : AM (List Level) := do
  let s ← get
  match s.caches.readLsC[h]? with
  | some us => pure us
  | none =>
    match denoteLs s.store.lss h with
    | none => failDanglingLs
    | some us =>
      let mp := s.caches.readLsC
      let s := { s with caches := { s.caches with readLsC := ∅ } }
      set { s with caches := { s.caches with readLsC := mp.insert h us } }
      pure us

/-- con-leche: none — the copy IS the function. -/
theorem readLevelM_eq (h : LIdx) : readLevelM h = readLevelMB h := rfl
/-- con-leche: none — the copy IS the function. -/
theorem readNameM_eq (h : NIdx) : readNameM h = readNameMB h := rfl
/-- con-leche: none — the copy IS the function. -/
theorem readLevelsM_eq (h : LsIdx) : readLevelsM h = readLevelsMB h := rfl

/-! ## 4. The three readback specs, with the frame

Same conclusions as `Bridge/Specs.lean`'s, plus the frame.  The answer's
VALUE is recovered inside the postcondition rather than taken as a parameter
— task #97-P3-0's rule 4, without which every caller's side goal carries a
metavariable. -/

/-- con-leche: ConLeche/Kernel/Expr.lean:41-46 Level — `readLevelM` with the
frame. -/
theorem readLevelMB_frame (s₀ : AState) (h : LIdx)
    (hc : ReadLCacheOK s₀.caches.readLC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevelMB h
    ⦃⇓? x s' => ⌜denoteL s₀.store.ls h = some x ∧ ReadbackFrame s₀ s'⌝⦄ := by
  mvcgen [readLevelMB]
  all_goals (bridge_peel; subst_vars)
  all_goals
    first
      | (intro hf; exact False.elim hf)
      | (refine ⟨by grind [ReadLCacheOK],
            ⟨rfl, rfl, rfl, rfl, ?_, id, id⟩⟩
         intro _
         grind [ReadLCacheOK])

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — `readNameM` with the
frame. -/
theorem readNameMB_frame (s₀ : AState) (h : NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readNameMB h
    ⦃⇓? x s' => ⌜denoteN s₀.store.ns h = some x ∧ ReadbackFrame s₀ s'⌝⦄ := by
  mvcgen [readNameMB]
  all_goals (bridge_peel; subst_vars)
  all_goals
    first
      | (intro hf; exact False.elim hf)
      | (refine ⟨by grind [ReadNCacheOK],
            ⟨rfl, rfl, rfl, rfl, id, ?_, id⟩⟩
         intro _
         grind [ReadNCacheOK])

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — `readLevelsM` with the
frame. -/
theorem readLevelsMB_frame (s₀ : AState) (h : LsIdx)
    (hc : ReadLsCacheOK s₀.caches.readLsC s₀.store) :
    ⦃fun s => ⌜s = s₀⌝⦄ readLevelsMB h
    ⦃⇓? us s' => ⌜denoteLs s₀.store.lss h = some us ∧
        ReadbackFrame s₀ s'⌝⦄ := by
  mvcgen [readLevelsMB]
  all_goals (bridge_peel; subst_vars)
  all_goals
    first
      | (intro hf; exact False.elim hf)
      | (refine ⟨by grind [ReadLsCacheOK],
            ⟨rfl, rfl, rfl, rfl, id, id, ?_⟩⟩
         intro _
         grind [ReadLsCacheOK])

end ConRon.Bridge.Core
