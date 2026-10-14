/-
# `ConRon.Bridge.ExprOps.InstLP` — Theorem 1 for the level helpers of `instLPGo`

DESIGN §8.2's Theorem 1 at the three LEVEL helpers of `Arena/ExprOps.lean`
that `instLPGo` (`ExprOps/Owed.lean`) calls: `substLevelList`, and the two
memoised substitutions `substLMemoAt` / `substLsMemoAt` of its `.sort` and
`.const` arms.

## Why the level work is an EQUATION and not a simulation

DESIGN §8.3's lesson 4 ("Levels and names: intern the representation, not
the algorithm").  `readLevelM` / `readLevelsM` ARE `denoteL` / `denoteLs`
(`Bridge/Specs.lean`'s `readLevelM_spec` is an equation), so the two memoised
substitutions run **con-leche's own** `Level.subst` on a transient tree and
re-intern the answer (`Bridge/SpecsL.lean`'s `internLevel_spec`,
`internLevels_spec`).  Nothing in this file simulates a level algorithm; the
level obligations are `Level.subst`-shaped facts about `denoteL`.

## The proofs

Each is `sym only [bridge_grind, …] => vcgen [f] <;> finish`: the answer
relations are `Bridge/Grind.lean` §3's `MapRel` equations, the memo hit is
the guarded `MemoLOK.get` / `MemoLsOK.get` below, the insert is
`ExprOps/MemoSpecs.lean`'s `instLP*Set_specI`, and the readback cache clauses
travel along the store order (§2).
-/
import ConRon.Bridge.ExprOps.MemoSpecs
import ConRon.Bridge.SpecsL

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## Vocabulary candidates (for Bridge/Grind.lean)

The level memo invariants' hits (`Bridge/Grind.lean` §5's shape: guarded at
the probe the program matched; their inserts are `MemoSpecs.lean`'s
`instLP*Set_specI` posts), and a level or level-list handle known only to
denote denotes SOMETHING (§3's `denote_some_of_isSome` at the level stores). -/

grind_pattern [bridge_grind] MemoLOK.get => MemoLOK f tbl st, tbl[k]?, some r where
  guard tbl[k]? = some r

grind_pattern [bridge_grind] MemoLsOK.get => MemoLsOK f tbl st, tbl[k]?, some r where
  guard tbl[k]? = some r

/-- con-leche: none — `denote_some_of_isSome` at a level handle. -/
@[bridge_grind →] theorem denoteL_some_of_isSome {st : LStore} {h : LIdx}
    (hs : (denoteL st h).isSome = true) : ∃ u, denoteL st h = some u :=
  Option.isSome_iff_exists.mp hs

/-- con-leche: none — `denote_some_of_isSome` at a universe-argument list
handle. -/
@[bridge_grind →] theorem denoteLs_some_of_isSome {st : LsStore} {h : LsIdx}
    (hs : (denoteLs st h).isSome = true) : ∃ us, denoteLs st h = some us :=
  Option.isSome_iff_exists.mp hs

-- A hit's cache frame is structure eta at the cache record (as in
-- `MemoSpecs.lean`).
attribute [local bridge_grind ext] Caches

/-! ## `substLevelList` — `Arena/ExprOps.lean:1901`

con-leche writes `vs.map (Level.subst ks us)`; DESIGN §3.4 forbids the closure
in code Aeneas must translate, so the twin is explicit recursion.  Theorem 1
is therefore an EQUATION between the two pure functions, with no state in
it. -/

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — **THEOREM 1 for
`substLevelList`**: the explicit recursion is con-leche's `.map`. -/
theorem substLevelList_eq (ks : List ConLeche.Name) (us : List Level) :
    ∀ vs : List Level, substLevelList ks us vs = vs.map (Level.subst ks us) := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v rest ih => simp only [substLevelList, List.map_cons, ih]

/-! ## `substLMemoAt` / `substLsMemoAt` — `Arena/ExprOps.lean:1914`, `:1925`

The level substitution behind its per-call memo.  Both are
"probe, else read back, run con-leche's function, re-intern, record": the
readback is `denoteL` / `denoteLs` by `readLevelM_spec` / `readLevelsM_spec`,
so the answer relation is `RelL` / `RelLs` at con-leche's `Level.subst`
without a single level lemma.

**The frame is not `s'.caches = s₀.caches`**: the memoised readback writes
`caches.readLC` / `caches.readLsC`.  What the caller gets instead is the two
readback clauses preserved — which is what `instLPGo` needs to call them
again — and the RECORD equation `s'.caches = { s₀.caches with readLC := … }`,
which frames the *other thirteen* cache tables in one line.  That is what
carries `ReadNCacheOK` across `instLPGo` and so lets `instLPFast_spec` state
a cache frame at all. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
**THEOREM 1 for `substLMemoAt`**: the memoised level substitution answers
`Level.subst ks us` of what the key denotes. -/
theorem substLMemoAt_spec (s₀ : AState) (ks : List ConLeche.Name)
    (us : List Level) (u : LIdx) (hok : StateOK s₀)
    (hm : InstLPLMemoA ks us s₀)
    (hc : ReadLCacheOK s₀.caches.readLC s₀.store)
    (hu : (denoteL s₀.store.ls u).isSome = true) :
    ⦃fun s => s = s₀⦄ substLMemoAt ks us u
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.pins = s₀.pins ∧
        s'.memos.instLPC = s₀.memos.instLPC ∧
        s'.memos.instLPLsC = s₀.memos.instLPLsC ∧
        InstLPLMemoA ks us s' ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        s'.caches = { s₀.caches with readLC := s'.caches.readLC } ∧
        RelL (Level.subst ks us) s₀.store u s'.store r; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind] => vcgen [substLMemoAt] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
**THEOREM 1 for `substLsMemoAt`**: the same at a universe-argument LIST
handle, whose answer is con-leche's `vs.map (Level.subst ks us)` by
`substLevelList_eq`. -/
theorem substLsMemoAt_spec (s₀ : AState) (ks : List ConLeche.Name)
    (us : List Level) (vs : LsIdx) (hok : StateOK s₀)
    (hm : InstLPLsMemoA ks us s₀)
    (hc : ReadLsCacheOK s₀.caches.readLsC s₀.store)
    (hvs : (denoteLs s₀.store.lss vs).isSome = true) :
    ⦃fun s => s = s₀⦄ substLsMemoAt ks us vs
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.pins = s₀.pins ∧
        s'.memos.instLPC = s₀.memos.instLPC ∧
        s'.memos.instLPLC = s₀.memos.instLPLC ∧
        InstLPLsMemoA ks us s' ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        s'.caches = { s₀.caches with readLsC := s'.caches.readLsC } ∧
        RelLs (fun ws => ws.map (Level.subst ks us)) s₀.store vs s'.store r; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind, substLevelList_eq] => vcgen [substLsMemoAt] <;> finish

end ConRon.Bridge.ExprOps
