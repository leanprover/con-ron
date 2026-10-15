/-
# `ConRon.Bridge.Core.Memo` — the memo wrappers of the knot's slots

DESIGN §8.2, and `_tmp/t97/conleche-arena-history.md` §2.3's middle piece:
between the body walks (`Bridge/Core/Arms/*.lean`) and the fuel induction
(`Bridge/Core/Induction.lean`) sit **the memo wrapper steps** — con-leche's
`Verify/Cached/KnotC.lean`, whose `memoEI_*_sim` / `memoBI_defeq_sim`
theorems are the same as this module's six wrapper steps (five slots, the
`whnfCore` slot in its two cheap modes).  The eager slot has no memo of its
own: it runs the eager tower's body under EMPTY mode-dependent memos and puts
the caller's back (`memoDefeqE_step`, at the end of the module).

A slot of `Arena/Core.lean`'s `coreKnot` at `fuel + 1` is

```lean
fun d e => do
  if whnfCoreStuckTag e then pure e          -- the stuck-tag lever (DESIGN, task #97-P6-7)
  else match (← get).caches.whnfCoreC[e]? with
  | some x => pure x                          -- the HIT
  | none   => do let x ← whnfCoreBody …; whnfCoreSet e x; pure x
```

so the wrapper has **three** branches where con-leche's `memoEI` has two, and
the extra one is the arena's own: the six head kinds `whnfCoreBody` returns
unchanged are read off the handle's tag without touching the store at all.
Its obligation is `whnfCoreBody e = pure e` at those tags — below, as
`denote_stuck_of_whnfCoreStuckTag` and `whnfCore_of_stuck` — and it is where
DESIGN §8.3's "index inequality IS structural inequality" is cashed for the
first time in the Core tier.

The other two branches are con-leche's:

* **the hit** consumes `CacheOK`'s clause at the query key.  The clause is
  depth-universal (`∃ F, ∀ d, a.wscopedB d → op F d a = .ok b`, the history
  report's lesson 8), so it yields the pure run at the CALL's depth with no
  further work — which is the whole reason the depth is not in the key;
* **the miss** runs the body walk and re-inserts, and the insert is where the
  run has to be made depth-universal again.  con-leche's own
  depth-invariance theorems (`Verify/Deep.lean:3066-3120`) are what does it,
  and they are the reason this module imports con-leche's `Verify` tier at
  all.

## The proofs: `vcgen` and `grind`

Each wrapper is `sym only [bridge_grind] => vcgen [the body's spec] <;> finish`:
`vcgen` generates the verification conditions inside `grind`'s symbolic
state, and `finish` closes each in the same E-graph from the three arm lemmas
of §3 (registered with `@[bridge_grind]`) and `Bridge/Grind.lean`'s
vocabulary (the store order, the state invariant's projections).  No custom
tactic, no addressing of a condition.

## No cap

The tables have no size cap (con-leche's `memoEI` has none): a setter is a
plain insert.
-/
import ConRon.Bridge.Core.Knot
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## 1. The knot's slots, unfolded once

A definition the verification condition generator would rewrite forever
needs its clauses as lemmas (DESIGN, task #97-P3-0, rule 9).  `coreKnot`
recurses on the fuel, so one `rfl` per slot at `fuel + 1` unfolds it exactly once — and,
because the arena's knot carries its memo probes INLINE (DESIGN, task #97c,
deviation 6), these equations are also the only place in the bridge where
the probe's shape is written down. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI — the
`whnfCore` slot at `fuel + 1`. -/
theorem coreKnot_whnfCore_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).whnfCore false d i =
      (do
        if whnfCoreStuckTag i then pure i
        else
        match (← get).caches.whnfCoreC[i]? with
        | some x => pure x
        | none => do
          let x ← whnfCoreBody mode (coreKnot mode fe id fuel) fe false d i
          whnfCoreSet i x
          pure x) := rfl

/-- con-leche: ConLeche/Cached/CoreC.lean:1945-2021 coreKnotI — the CHEAP
`whnfCore` slot at `fuel + 1`, under its own table. -/
theorem coreKnot_whnfCoreCheap_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).whnfCore true d i =
      (do
        if whnfCoreStuckTag i then pure i
        else
        match (← get).caches.whnfCoreCheapC[i]? with
        | some x => pure x
        | none => do
          let x ← whnfCoreBody mode (coreKnot mode fe id fuel) fe true d i
          whnfCoreCheapSet i x
          pure x) := rfl

/-- con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI — the `whnf`
slot at `fuel + 1`. -/
theorem coreKnot_whnf_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).whnf d i =
      (do
        if whnfStuckTag i then pure i
        else
        match (← get).caches.whnfC[i]? with
        | some x => pure x
        | none => do
          let x ← whnfBody (coreKnot mode fe id fuel) fe d i
          whnfSet i x
          pure x) := rfl

/-- con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI — the `infer`
slot at `fuel + 1`. -/
theorem coreKnot_infer_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).infer d i =
      (do
        match (← get).caches.inferC[i]? with
        | some x => pure x
        | none => do
          let x ← inferBody (coreKnot mode fe id fuel) fe d i
          inferSet i x
          pure x) := rfl

/-- con-leche: ConLeche/Cached/CoreC.lean:1893-1906 memoBI — the `defeq` slot
at `fuel + 1`, keyed on the ORDERED pair with the verdict. -/
theorem coreKnot_defeq_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (a b : EIdx) :
    (coreKnot mode fe id (fuel + 1)).defeq d a b =
      (do
        match (← get).caches.defeqC[(a, b)]? with
        | some x => pure x
        | none => do
          let x ← defeqBody mode (coreKnot mode fe id fuel) fe d a b
          defeqSet a b x
          pure x) := rfl

/-- con-leche: ConLeche/Cached/CoreC.lean:1493-1565 coreKnotI — the eager
slot at `fuel + 1`: the body at `mode.toEager` over the knot at `mode.toEager`
one level down, between detaching the caller's mode-dependent memos and
putting them back (con-leche's `withFreshMemos`). -/
theorem coreKnot_defeqE_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (a b : EIdx) :
    (coreKnot mode fe id (fuel + 1)).defeqE d a b =
      (do
        let saved ← takeModeMemos
        let x ← defeqBody mode.toEager (coreKnot mode.toEager fe id fuel) fe d a b
        putModeMemos saved
        pure x) := rfl

/-- con-leche: ConLeche/Cached/CoreC.lean:1966-1979 coreKnotI — the `inferIO`
slot at `fuel + 1`: the io body under the io-grade view of the knot one
level down, at every mode (con-leche task #346). -/
theorem coreKnot_inferIO_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).inferIO d i =
      (do
        match (← get).caches.inferIOC[i]? with
        | some x => pure x
        | none => do
          let x ← inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
          inferIOSet i x
          pure x) := rfl

/-! ## 2. The six cache setters' specs

One equation each, a plain insert.  Stated as a whole
`AState` equality rather than as a table equation plus thirteen frames: the
setter is one `set` of one record update, so the equation IS the spec and
every frame condition a caller needs falls out of it by `simp`. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `whnfCoreSet`
replaces exactly one field of one record. -/
@[spec] theorem whnfCoreSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => s = s₀⦄ whnfCoreSet e r
    ⦃fun _u s' => s' = { s₀ with caches := { s₀.caches with
        whnfCoreC := s₀.caches.whnfCoreC.insert e r } }; ⊤⦄ := by
  dsimp only
  vcgen [whnfCoreSet] with finish

/-- con-leche: ConLeche/Cached/CoreC.lean:1910-1928 memoEI — `whnfCoreCheapSet`
replaces exactly one field of one record. -/
@[spec] theorem whnfCoreCheapSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => s = s₀⦄ whnfCoreCheapSet e r
    ⦃fun _u s' => s' = { s₀ with caches := { s₀.caches with
        whnfCoreCheapC := s₀.caches.whnfCoreCheapC.insert e r } }; ⊤⦄ := by
  dsimp only
  vcgen [whnfCoreCheapSet] with finish

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `whnfSet`. -/
@[spec] theorem whnfSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => s = s₀⦄ whnfSet e r
    ⦃fun _u s' => s' = { s₀ with caches := { s₀.caches with
        whnfC := s₀.caches.whnfC.insert e r } }; ⊤⦄ := by
  dsimp only
  vcgen [whnfSet] with finish

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `inferSet`. -/
@[spec] theorem inferSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => s = s₀⦄ inferSet e r
    ⦃fun _u s' => s' = { s₀ with caches := { s₀.caches with
        inferC := s₀.caches.inferC.insert e r } }; ⊤⦄ := by
  dsimp only
  vcgen [inferSet] with finish

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `inferIOSet`, in
the io grade's own table. -/
@[spec] theorem inferIOSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => s = s₀⦄ inferIOSet e r
    ⦃fun _u s' => s' = { s₀ with caches := { s₀.caches with
        inferIOC := s₀.caches.inferIOC.insert e r } }; ⊤⦄ := by
  dsimp only
  vcgen [inferIOSet] with finish

/-- con-leche: ConLeche/Cached/CoreC.lean:1893-1906 memoBI — `defeqSet`, at
the ORDERED pair and with the verdict. -/
@[spec] theorem defeqSet_spec (s₀ : AState) (a b : EIdx) (r : Bool) :
    ⦃fun s => s = s₀⦄ defeqSet a b r
    ⦃fun _u s' => s' = { s₀ with caches := { s₀.caches with
        defeqC := s₀.caches.defeqC.insert (a, b) r } }; ⊤⦄ := by
  dsimp only
  vcgen [defeqSet] with finish

/-- con-leche: ConLeche/Cached/StateC.lean:336-342 CState.takeModeMemos —
`takeModeMemos` empties the six mode-dependent tables and returns them. -/
theorem takeModeMemos_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ takeModeMemos
    ⦃fun mm s' => mm = ⟨s₀.caches.whnfCoreC, s₀.caches.whnfCoreCheapC, s₀.caches.whnfC,
          s₀.caches.inferC, s₀.caches.inferIOC, s₀.caches.defeqC⟩ ∧
        s' = { s₀ with caches :=
          { s₀.caches with
            whnfCoreC := ∅, whnfCoreCheapC := ∅, whnfC := ∅,
            inferC := ∅, inferIOC := ∅, defeqC := ∅ } }; ⊤⦄ := by
  vcgen [takeModeMemos] with finish

/-- con-leche: ConLeche/Cached/StateC.lean:344-348 CState.putModeMemos —
`putModeMemos` replaces the six mode-dependent tables. -/
theorem putModeMemos_spec (s₀ : AState) (mm : ModeMemos) :
    ⦃fun s => s = s₀⦄ putModeMemos mm
    ⦃fun _u s' => s' = { s₀ with caches :=
        { s₀.caches with
          whnfCoreC := mm.whnfCoreC, whnfCoreCheapC := mm.whnfCoreCheapC,
          whnfC := mm.whnfC, inferC := mm.inferC,
          inferIOC := mm.inferIOC, defeqC := mm.defeqC } }; ⊤⦄ := by
  vcgen [putModeMemos] with finish

/-! ## 3. The cache invariant under an insert

con-leche's `CSOK.insert*` (`Verify/Cached/KnotC.lean:51-174`), through the
generic lemma so that the six per-table versions are one line each. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC — the
generic entry-cache insert.  The row's backing is the depth-universal run,
which is exactly what the wrapper's miss branch builds from the body's answer
plus con-leche's depth invariance. -/
theorem EntryCacheOK.insert {op : Nat → Nat → Expr → CheckM Expr}
    {tbl : Std.HashMap EIdx EIdx} {st : EStore} (h : EntryCacheOK op tbl st)
    {i j : EIdx} {a b : Expr} (ha : denoteE st i = some a)
    (hb : denoteE st j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true → op F d a = .ok b) :
    EntryCacheOK op (tbl.insert i j) st := by
  intro i' j' hl
  rw [Std.HashMap.getElem?_insert] at hl
  split at hl
  · rename_i hbeq
    cases hl
    obtain rfl := eq_of_beq hbeq
    exact ⟨a, b, ha, hb, hrun⟩
  · exact h i' j' hl

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:146 CSOK.insertDefeqC — the
`defeq` verdict cache's insert, BOTH SIGNS (the row carries the `Bool` the
pure run answered). -/
theorem DefeqCacheOK.insert {op : Nat → Nat → Expr → Expr → CheckM Bool}
    {tbl : Std.HashMap (EIdx × EIdx) Bool} {st : EStore}
    (h : DefeqCacheOK op tbl st) {i j : EIdx} {a b : Expr} {x : Bool}
    (ha : denoteE st i = some a) (hb : denoteE st j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true → Expr.wscopedB d b = true →
      op F d a b = .ok x) :
    DefeqCacheOK op
      (tbl.insert (i, j) x) st := by
  have key : ∀ (t : Std.HashMap (EIdx × EIdx) Bool), DefeqCacheOK op t st →
      DefeqCacheOK op (t.insert (i, j) x) st := by
    intro t ht k r hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    · rename_i hbeq
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨a, b, ha, hb, hrun⟩
    · exact ht k r hl
  exact key _ h

/-! ### The six per-table versions

Each rebuilds `CacheOK` from the thirteen clauses that did not move plus the
one that did.  `CacheOK` is a flat fourteen-field structure, so the pattern is
mechanical; the reason it is not one generic lemma is that the field being
updated is different in each. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC. -/
theorem CacheOK.insertWhnfCore {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.whnfCore mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      whnfCoreC := s.caches.whnfCoreC.insert i j } } :=
  { hc with whnfCore := EntryCacheOK.insert hc.whnfCore ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean CSOK.insertWhnfCoreCheapC. -/
theorem CacheOK.insertWhnfCoreCheap {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.whnfCore mode env F d a true = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      whnfCoreCheapC := s.caches.whnfCoreCheapC.insert i j } } :=
  { hc with whnfCoreCheap := EntryCacheOK.insert hc.whnfCoreCheap ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:69 CSOK.insertWhnfC. -/
theorem CacheOK.insertWhnf {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.whnf mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      whnfC := s.caches.whnfC.insert i j } } :=
  { hc with whnf := EntryCacheOK.insert hc.whnf ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:87 CSOK.insertInferC. -/
theorem CacheOK.insertInfer {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.inferTypeCore mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      inferC := s.caches.inferC.insert i j } } :=
  { hc with infer := EntryCacheOK.insert hc.infer ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:108 CSOK.insertInferIOC. -/
theorem CacheOK.insertInferIO {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.inferTypeIO mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      inferIOC := s.caches.inferIOC.insert i j } } :=
  { hc with inferIO := EntryCacheOK.insert hc.inferIO ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:146 CSOK.insertDefeqC. -/
theorem CacheOK.insertDefeq {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr} {x : Bool}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true → Expr.wscopedB d b = true →
      ConLeche.isDefEqCore mode env F d a b = .ok x) :
    CacheOK mode env { s with caches := { s.caches with
      defeqC := s.caches.defeqC.insert (i, j) x } } :=
  { hc with defeq := DefeqCacheOK.insert hc.defeq ha hb hrun }

/-! ### `CheckOK` past a cache insert

The store, the pins and the environment index do not move, so the whole
invariant follows from the cache clause alone. -/

/-- con-leche: none — `CheckOK` from `CacheOK` at a state whose store, pins
and index are the old ones (at any mode: only the cache clause names one). -/
theorem CheckOK.ofCache {mode mode' : CheckMode} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK mode' env fe s) (hc : CacheOK mode env s')
    (hst : s'.store = s.store) (hp : s'.pins = s.pins) :
    CheckOK mode env fe s' where
  state := ⟨hst ▸ h.state.wf⟩
  caches := hc
  pins := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hst, hp] <;>
      first
        | exact h.pins.ready | exact h.pins.names | exact h.pins.reserved
        | exact h.pins.emptyLevels | exact h.pins.zeroLevel
        | exact h.pins.sortOne | exact h.pins.anon
  ienv := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hst]
    · exact h.ienv.hit
    · exact h.ienv.cover
    · exact h.ienv.proj


/-! ### The three arms of a memo wrapper, as lemmas

Every wrapper of §5 has the same three exits — the stuck tag, the cache hit,
the miss re-inserted — and each is one lemma here, stated in the shape the
verification condition has and registered with `@[bridge_grind]`, so that
each wrapper's proof is `vcgen` with `finish` (`Bridge/Grind.lean`), not a
list of arms.  Every variable of a registered lemma occurs in its pattern: the
miss lemmas take the body's answer as ONE premise (`SimE`/`SimV`, the
callee's own postcondition atom) instead of its parts, whose answer and fuel
`grind` could not bind; the hit lemmas' patterns name the state invariant and
the table probe besides the answer.
`row_of_run` is the depth-universal row from one run at the query's depth
(the history report's lesson 8). -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — **a `SimE` answer, opened**:
the answer handle's denotation, its scope and the run, for a
caller that composes the answer with another walk's. -/
theorem SimE.inv {op : Nat → Nat → Expr → CheckM Expr} {d : Nat} {e : Expr}
    {st : EStore} {r : EIdx} (h : SimE op d e st r) :
    ∃ v, denoteE st r = some v ∧ Expr.WScoped d v ∧ ∃ F, op F d e = .ok v := h
grind_pattern [bridge_grind] SimE.inv => SimE op d e st r

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
the depth-universal row a miss inserts, from the one run at the query's
depth and the slot's depth invariance. -/
theorem row_of_run {P : Nat → Nat → Expr → CheckM Expr}
    (hdep : ∀ F d₁ d₂ e, Expr.wscopedB d₁ e = true → Expr.wscopedB d₂ e = true →
      P F d₁ e = P F d₂ e)
    {F d : Nat} {a b : Expr} (hw : Expr.WScoped d a) (hF : P F d a = .ok b) :
    ∃ F, ∀ d', Expr.wscopedB d' a = true → P F d' a = .ok b :=
  ⟨F, fun d' hd' => by rw [hdep F d' d a hd' hw.to_wscopedB]; exact hF⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the hit**: a row of a depth-universal table answers the query at its own
depth, with the slot's scope preservation. -/
theorem SimE.of_row {P : Nat → Nat → Expr → CheckM Expr}
    (hpres : ∀ F d a b, P F d a = .ok b → Expr.WScoped d a → Expr.WScoped d b)
    {st : EStore} {i j : EIdx} {d : Nat} {e : Expr}
    (hrow : ∃ a b, denoteE st i = some a ∧ denoteE st j = some b ∧
      ∃ F, ∀ d, Expr.wscopedB d a = true → P F d a = .ok b)
    (hden : denoteE st i = some e) (hw : Expr.WScoped d e) : SimE P d e st j := by
  obtain ⟨a, b, ha, hb, F, hall⟩ := hrow
  rw [hden] at ha
  obtain rfl := Option.some.inj ha
  have hrun := hall d hw.to_wscopedB
  exact ⟨b, hb, hpres F d _ _ hrun hw, F, hrun⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the hit** at each table, from the state invariant (its pattern names the
answer, the invariant and the probe, so that `grind` binds `fe` and `i`). -/
@[bridge_grind .] theorem CheckOK.whnfCoreHit {mode : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    {i j : EIdx} {d : Nat} {e : Expr} (henv : ConLeche.EnvWF env)
    (hok : CheckOK mode env fe s) (hx : s.caches.whnfCoreC[i]? = some j)
    (hden : denoteE s.store i = some e) (hw : Expr.WScoped d e) :
    SimE (fun F d e => ConLeche.whnfCore mode env F d e false) d e s.store j :=
  SimE.of_row (fun F _ _ _ h hw => ConLeche.whnfCore_WScoped henv F h hw)
    (hok.caches.whnfCore _ _ hx) hden hw

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
the hit, cheap mode. -/
@[bridge_grind .] theorem CheckOK.whnfCoreCheapHit {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {i j : EIdx} {d : Nat} {e : Expr} (henv : ConLeche.EnvWF env)
    (hok : CheckOK mode env fe s) (hx : s.caches.whnfCoreCheapC[i]? = some j)
    (hden : denoteE s.store i = some e) (hw : Expr.WScoped d e) :
    SimE (fun F d e => ConLeche.whnfCore mode env F d e true) d e s.store j :=
  SimE.of_row (fun F _ _ _ h hw => ConLeche.whnfCore_WScoped henv F h hw)
    (hok.caches.whnfCoreCheap _ _ hx) hden hw

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:230 memoEI_whnf_sim — the
hit, `whnf`. -/
@[bridge_grind .] theorem CheckOK.whnfHit {mode : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    {i j : EIdx} {d : Nat} {e : Expr} (henv : ConLeche.EnvWF env)
    (hok : CheckOK mode env fe s) (hx : s.caches.whnfC[i]? = some j)
    (hden : denoteE s.store i = some e) (hw : Expr.WScoped d e) :
    SimE (ConLeche.whnf mode env) d e s.store j :=
  SimE.of_row (fun F _ _ _ h hw => ConLeche.whnf_WScoped henv F h hw)
    (hok.caches.whnf _ _ hx) hden hw

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:283 memoEI_infer_sim — the
hit, `infer`. -/
@[bridge_grind .] theorem CheckOK.inferHit {mode : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    {i j : EIdx} {d : Nat} {e : Expr} (henv : ConLeche.EnvWF env)
    (hok : CheckOK mode env fe s) (hx : s.caches.inferC[i]? = some j)
    (hden : denoteE s.store i = some e) (hw : Expr.WScoped d e) :
    SimE (ConLeche.inferTypeCore mode env) d e s.store j :=
  SimE.of_row (fun F _ _ _ h hw => ConLeche.inferTypeCore_WScoped henv F h hw)
    (hok.caches.infer _ _ hx) hden hw

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:341 memoEI_inferIO_sim — the
hit, the io grade. -/
@[bridge_grind .] theorem CheckOK.inferIOHit {mode : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    {i j : EIdx} {d : Nat} {e : Expr} (henv : ConLeche.EnvWF env)
    (hok : CheckOK mode env fe s) (hx : s.caches.inferIOC[i]? = some j)
    (hden : denoteE s.store i = some e) (hw : Expr.WScoped d e) :
    SimE (ConLeche.inferTypeIO mode env) d e s.store j :=
  SimE.of_row (fun F _ _ _ h hw => ConLeche.inferTypeIO_WScoped henv F h hw)
    (hok.caches.inferIO _ _ hx) hden hw

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:463 memoBI_defeq_sim — the
hit, `defeq`: the row carries the verdict, so both signs are sound. -/
@[bridge_grind .] theorem CheckOK.defeqHit {mode : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    {i j : EIdx} {x : Bool} {d : Nat} {a b : Expr}
    (hok : CheckOK mode env fe s) (hx : s.caches.defeqC[(i, j)]? = some x)
    (hda : denoteE s.store i = some a) (hdb : denoteE s.store j = some b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    SimV (ConLeche.isDefEqCore mode env) d a b x := by
  obtain ⟨a', b', ha', hb', F, hall⟩ := hok.caches.defeq _ _ hx
  obtain rfl := Option.some.inj (ha'.symm.trans hda)
  obtain rfl := Option.some.inj (hb'.symm.trans hdb)
  exact ⟨F, hall d hwa.to_wscopedB hwb.to_wscopedB⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the miss**, full `whnfCore`: the body's answer re-inserted. -/
@[bridge_grind .] theorem CheckOK.insertWhnfCoreAt {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {i j : EIdx} {a : Expr} {d : Nat} (henv : ConLeche.EnvWF env)
    (hck : CheckOK mode env fe s) (ha : denoteE s.store i = some a)
    (hw : Expr.WScoped d a) (hs : SimE (fun F d e => ConLeche.whnfCore mode env F d e false) d a s.store j) :
    CheckOK mode env fe { s with caches := { s.caches with
      whnfCoreC := s.caches.whnfCoreC.insert i j } } :=
  let ⟨_, hb, _, _, hF⟩ := hs
  CheckOK.ofCache hck (CacheOK.insertWhnfCore hck.caches ha hb
    (row_of_run (P := fun F d e => ConLeche.whnfCore mode env F d e false)
      (fun F _ _ _ h1 h2 => ConLeche.whnfCore_depth_inv henv F h1 h2) hw hF)) rfl rfl

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the miss**, cheap `whnfCore`. -/
@[bridge_grind .] theorem CheckOK.insertWhnfCoreCheapAt {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {i j : EIdx} {a : Expr} {d : Nat} (henv : ConLeche.EnvWF env)
    (hck : CheckOK mode env fe s) (ha : denoteE s.store i = some a)
    (hw : Expr.WScoped d a) (hs : SimE (fun F d e => ConLeche.whnfCore mode env F d e true) d a s.store j) :
    CheckOK mode env fe { s with caches := { s.caches with
      whnfCoreCheapC := s.caches.whnfCoreCheapC.insert i j } } :=
  let ⟨_, hb, _, _, hF⟩ := hs
  CheckOK.ofCache hck (CacheOK.insertWhnfCoreCheap hck.caches ha hb
    (row_of_run (P := fun F d e => ConLeche.whnfCore mode env F d e true)
      (fun F _ _ _ h1 h2 => ConLeche.whnfCore_depth_inv henv F h1 h2) hw hF)) rfl rfl

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:230 memoEI_whnf_sim —
**the miss**, `whnf`. -/
@[bridge_grind .] theorem CheckOK.insertWhnfAt {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {i j : EIdx} {a : Expr} {d : Nat} (henv : ConLeche.EnvWF env)
    (hck : CheckOK mode env fe s) (ha : denoteE s.store i = some a)
    (hw : Expr.WScoped d a) (hs : SimE (ConLeche.whnf mode env) d a s.store j) :
    CheckOK mode env fe { s with caches := { s.caches with
      whnfC := s.caches.whnfC.insert i j } } :=
  let ⟨_, hb, _, _, hF⟩ := hs
  CheckOK.ofCache hck (CacheOK.insertWhnf hck.caches ha hb
    (row_of_run (P := ConLeche.whnf mode env)
      (fun F _ _ _ h1 h2 => ConLeche.whnf_depth_inv henv F h1 h2) hw hF)) rfl rfl

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:283 memoEI_infer_sim —
**the miss**, `infer`. -/
@[bridge_grind .] theorem CheckOK.insertInferAt {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {i j : EIdx} {a : Expr} {d : Nat} (henv : ConLeche.EnvWF env)
    (hck : CheckOK mode env fe s) (ha : denoteE s.store i = some a)
    (hw : Expr.WScoped d a) (hs : SimE (ConLeche.inferTypeCore mode env) d a s.store j) :
    CheckOK mode env fe { s with caches := { s.caches with
      inferC := s.caches.inferC.insert i j } } :=
  let ⟨_, hb, _, _, hF⟩ := hs
  CheckOK.ofCache hck (CacheOK.insertInfer hck.caches ha hb
    (row_of_run (P := ConLeche.inferTypeCore mode env)
      (fun F _ _ _ h1 h2 => ConLeche.inferTypeCore_depth_inv henv F h1 h2) hw hF)) rfl rfl

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:341 memoEI_inferIO_sim —
**the miss**, the io grade. -/
@[bridge_grind .] theorem CheckOK.insertInferIOAt {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {i j : EIdx} {a : Expr} {d : Nat} (henv : ConLeche.EnvWF env)
    (hck : CheckOK mode env fe s) (ha : denoteE s.store i = some a)
    (hw : Expr.WScoped d a) (hs : SimE (ConLeche.inferTypeIO mode env) d a s.store j) :
    CheckOK mode env fe { s with caches := { s.caches with
      inferIOC := s.caches.inferIOC.insert i j } } :=
  let ⟨_, hb, _, _, hF⟩ := hs
  CheckOK.ofCache hck (CacheOK.insertInferIO hck.caches ha hb
    (row_of_run (P := ConLeche.inferTypeIO mode env)
      (fun F _ _ _ h1 h2 => ConLeche.inferTypeIO_depth_inv henv F h1 h2) hw hF)) rfl rfl

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:463 memoBI_defeq_sim —
**the miss**, `defeq`: the verdict re-inserted at the pair. -/
@[bridge_grind .] theorem CheckOK.insertDefeqAt {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {i j : EIdx} {a b : Expr} {x : Bool} {d : Nat}
    (henv : ConLeche.EnvWF env)
    (hck : CheckOK mode env fe s) (ha : denoteE s.store i = some a)
    (hb : denoteE s.store j = some b) (hwa : Expr.WScoped d a)
    (hwb : Expr.WScoped d b) (hs : SimV (ConLeche.isDefEqCore mode env) d a b x) :
    CheckOK mode env fe { s with caches := { s.caches with
      defeqC := s.caches.defeqC.insert (i, j) x } } :=
  let ⟨F, hF⟩ := hs
  CheckOK.ofCache hck (CacheOK.insertDefeq hck.caches ha hb
    ⟨F, fun d' hda' hdb' => by
      rw [ConLeche.isDefEqCore_depth_inv henv F hda' hdb' hwa.to_wscopedB
        hwb.to_wscopedB]
      exact hF⟩) rfl rfl

/-! ## 4. The stuck-tag branch (DESIGN, task #97-P6-7)

The arena's third branch, which con-leche's `memoEI` has no counterpart for:
six head kinds are answered off the handle word alone, with neither a store
read nor a memo probe.  Its soundness obligation is that con-leche's own body
returns those six unchanged, and DESIGN §8.3's licence for reading the kind
off the tag is `EStore.tagOf_of_view` (`Bridge/Rel.lean`) — a handle carries
the tag of its own view on a well-formed store. -/

/-- con-leche: none — what `whnfCoreStuckTag` says about the tag. -/
theorem whnfCoreStuckTag_ne {h : EIdx} (hs : whnfCoreStuckTag h = true) :
    h.tag ≠ ETag.app ∧ h.tag ≠ ETag.proj ∧ h.tag ≠ ETag.letE ∧
      h.tag ≠ ETag.bvar := by
  simp only [whnfCoreStuckTag] at hs
  grind

/-- con-leche: none — what `whnfStuckTag` says about the tag: one of the five
kinds `whnfBody` cannot move. -/
theorem whnfStuckTag_eq {h : EIdx} (hs : whnfStuckTag h = true) :
    h.tag = ETag.sort ∨ h.tag = ETag.fvar ∨ h.tag = ETag.lam ∨
      h.tag = ETag.forallE ∨ h.tag = ETag.lit := by
  simp only [whnfStuckTag] at hs
  grind

/-- con-leche: ConLeche/Kernel/Core.lean:968-975 whnfCoreBody — **the
stuck-tag branch's shape obligation**: a handle whose tag is none of `app`,
`proj`, `letE`, `bvar` denotes one of the six constructors `whnfCoreBody`
returns unchanged. -/
theorem denote_stuck_of_whnfCoreStuckTag {st : EStore} (hwf : StoreWF st)
    {h : EIdx} {e : Expr} (he : denoteE st h = some e)
    (hs : whnfCoreStuckTag h = true) :
    (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨ (∃ n us, e = .const n us) ∨
      (∃ l, e = .lit l) ∨ (∃ t b, e = .lam t b) ∨
      (∃ t b, e = .forallE t b) := by
  obtain ⟨happ, hproj, hlet, hbvar⟩ := whnfCoreStuckTag_ne hs
  obtain ⟨v, hv⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hv
  cases v with
  | bvar i => exact absurd (htag.trans rfl) hbvar
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he
    exact Or.inl ⟨k, t', rfl⟩
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he
    exact Or.inr (Or.inl ⟨l, rfl⟩)
  | const n us =>
    obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv he
    exact Or.inr (Or.inr (Or.inl ⟨nm, ls, rfl⟩))
  | app f a => exact absurd (htag.trans rfl) happ
  | lam ty b =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hv he
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨et, eb, rfl⟩))))
  | forallE ty b =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv he
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨et, eb, rfl⟩))))
  | letE ty w b => exact absurd (htag.trans rfl) hlet
  | lit l =>
    rw [denote_lit_inv hwf hv he]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨l, rfl⟩)))
  | proj n i sub => exact absurd (htag.trans rfl) hproj

/-- con-leche: ConLeche/Kernel/Core.lean:968-975 whnfCoreBody — the six
constructors the body's first six clauses answer with themselves. -/
theorem whnfCore_of_stuck {mode : CheckMode} {env : Env} {e : Expr} {c : Bool}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l) ∨
      (∃ t b, e = .lam t b) ∨ (∃ t b, e = .forallE t b))
    (F d : Nat) : ConLeche.whnfCore mode env (F + 1) d e c = .ok e := by
  rw [ConLeche.whnfCore_succ]
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ |
      ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩ <;>
    simp [ConLeche.whnfCoreBody, pure, Except.pure]


/-- con-leche: ConLeche/Kernel/Core.lean:1097-1099 whnfBody — the same at the
reduction loop: a handle whose tag is `sort`, `fvar`, `lam`, `forallE` or
`lit` denotes one of those five. -/
theorem denote_stuck_of_whnfStuckTag {st : EStore} (hwf : StoreWF st)
    {h : EIdx} {e : Expr} (he : denoteE st h = some e)
    (hs : whnfStuckTag h = true) :
    (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨ (∃ t b, e = .lam t b) ∨
      (∃ t b, e = .forallE t b) ∨ (∃ l, e = .lit l) := by
  obtain ⟨v, hv⟩ := denoteE_view he
  have htag := EStore.tagOf_of_view hv
  have htg := whnfStuckTag_eq hs
  cases v with
  | bvar i => rw [htag] at htg; simp [ENodeView.tagOf, ETag.bvar, ETag.sort,
      ETag.fvar, ETag.lam, ETag.forallE, ETag.lit] at htg
  | fvar k t =>
    obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he
    exact Or.inl ⟨k, t', rfl⟩
  | sort u =>
    obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he
    exact Or.inr (Or.inl ⟨l, rfl⟩)
  | const n us => rw [htag] at htg; simp [ENodeView.tagOf, ETag.const,
      ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit] at htg
  | app f a => rw [htag] at htg; simp [ENodeView.tagOf, ETag.app, ETag.sort,
      ETag.fvar, ETag.lam, ETag.forallE, ETag.lit] at htg
  | lam ty b =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hv he
    exact Or.inr (Or.inr (Or.inl ⟨et, eb, rfl⟩))
  | forallE ty b =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv he
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨et, eb, rfl⟩)))
  | letE ty w b => rw [htag] at htg; simp [ENodeView.tagOf, ETag.letE,
      ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit] at htg
  | lit l =>
    rw [denote_lit_inv hwf hv he]
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩)))
  | proj n i sub => rw [htag] at htg; simp [ENodeView.tagOf, ETag.proj,
      ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit] at htg

/-- con-leche: ConLeche/Verify/Knot.lean:42 whnfCore_succ — the pure knot's
`whnfCore` slot at `F + 1`, in the record spelling `whnfBody` calls it by. -/
theorem pureFns_whnfCore_succ (mode : CheckMode) (env : Env) (F d : Nat) (e : Expr)
    (c : Bool) :
    (pureFns mode env (F + 1)).whnfCore c d e =
      ConLeche.whnfCoreBody mode (pureFns mode env F) env c d e := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1073-1099 whnfStep/whnfBody — the
five constructors the reduction loop cannot move: `whnfCore` returns them
unchanged, `reduceNat`'s match needs an `.app` and `unfoldDefinition`'s needs
a `.const` head, so the first iteration of the loop is `pure e`.  **Two fuel
levels**, because the loop's own `whnfCore` call consumes one. -/
theorem whnf_of_stuck {mode : CheckMode} {env : Env} {e : Expr}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ t b, e = .lam t b) ∨ (∃ t b, e = .forallE t b) ∨
      (∃ l, e = .lit l))
    (F d : Nat) : ConLeche.whnf mode env (F + 2) d e = .ok e := by
  obtain ⟨n, hn⟩ := ConLeche.whnfLoopFuel_succ
  rw [show F + 2 = (F + 1) + 1 from rfl, ConLeche.whnf_succ,
    ConLeche.whnfBody, hn, ConLeche.whnfLoop, ConLeche.whnfStep]
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨t, b, rfl⟩ | ⟨t, b, rfl⟩ |
      ⟨l, rfl⟩ <;>
    simp [pureFns_whnfCore_succ, ConLeche.whnfCoreBody, ConLeche.reduceNat,
      ConLeche.unfoldDefinition, ConLeche.Expr.getAppFn, pure, Except.pure,
      bind, Except.bind]


/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the stuck tag** of the `whnfCore` wrappers: the pure body answers with its
own argument.  Not registered: its operation is a `fun` over `mode`, `env`
and `c`, which no pattern can bind, so a wrapper passes it instantiated. -/
theorem SimE.of_whnfCoreStuck {mode : CheckMode} {env : Env} {c : Bool}
    {st : EStore} {i : EIdx} {d : Nat} {e : Expr} (hwf : StoreWF st)
    (hs : whnfCoreStuckTag i = true) (hden : denoteE st i = some e)
    (hw : Expr.WScoped d e) :
    SimE (fun F d e => ConLeche.whnfCore mode env F d e c) d e st i :=
  ⟨e, hden, hw, 1, whnfCore_of_stuck (denote_stuck_of_whnfCoreStuckTag hwf hden hs) 0 d⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:230 memoEI_whnf_sim — the
stuck tag of the `whnf` wrapper. -/
@[bridge_grind .] theorem SimE.of_whnfStuck {mode : CheckMode} {env : Env}
    {st : EStore} {i : EIdx} {d : Nat} {e : Expr} (hwf : StoreWF st)
    (hs : whnfStuckTag i = true) (hden : denoteE st i = some e)
    (hw : Expr.WScoped d e) :
    SimE (ConLeche.whnf mode env) d e st i :=
  ⟨e, hden, hw, 2, whnf_of_stuck (denote_stuck_of_whnfStuckTag hwf hden hs) 0 d⟩

/-! ## 5. The six memo-wrapper steps

con-leche's `Verify/Cached/KnotC.lean:175-529`, one per slot: from the body
walk at fuel `f`, the SLOT at fuel `f + 1`. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the `whnfCore` wrapper**, full mode: stuck tag, cache hit, cache miss. -/
theorem memoWhnfCoreFull_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (whnfCoreBody mode (coreKnot mode fe id fuel) fe false)
      (fun F d e => ConLeche.whnfCore mode env F d e false))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).whnfCore false d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (fun F d e => ConLeche.whnfCore mode env F d e false) d e s'.store r; ⊤⦄ := by
  rw [coreKnot_whnfCore_succ]
  -- the body spec at THIS subject: `e` does not occur in the program, so
  -- `vcgen` would not solve it by unification (as `memoDefeq_step` notes);
  -- the stuck-tag lemma at THIS slot: its answer's operation is a `fun`, so
  -- the registered form would have no pattern for `mode`, `env`, `c`
  sym only [bridge_grind, SimE.of_whnfCoreStuck (mode := mode) (env := env) (c := false)] =>
    vcgen [fun s₁ h1 h2 => hbody s₁ d i e h1 h2 hw] <;> finish

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the `whnfCore` wrapper**, CHEAP mode (official `cheap_proj`), under the
cheap mode's own table. -/
theorem memoWhnfCoreCheap_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (whnfCoreBody mode (coreKnot mode fe id fuel) fe true)
      (fun F d e => ConLeche.whnfCore mode env F d e true))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).whnfCore true d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (fun F d e => ConLeche.whnfCore mode env F d e true) d e s'.store r; ⊤⦄ := by
  rw [coreKnot_whnfCoreCheap_succ]
  sym only [bridge_grind, SimE.of_whnfCoreStuck (mode := mode) (env := env) (c := true)] =>
    vcgen [fun s₁ h1 h2 => hbody s₁ d i e h1 h2 hw] <;> finish

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the `whnfCore` wrapper** in either mode. -/
theorem memoWhnfCore_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : ∀ c, BodySpec mode env fe
      (whnfCoreBody mode (coreKnot mode fe id fuel) fe c)
      (fun F d e => ConLeche.whnfCore mode env F d e c))
    {c : Bool} (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).whnfCore c d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (fun F d e => ConLeche.whnfCore mode env F d e c) d e s'.store r; ⊤⦄ := by
  cases c
  · exact memoWhnfCoreFull_step henv (hbody false) s₀ d i e hok hden hw
  · exact memoWhnfCoreCheap_step henv (hbody true) s₀ d i e hok hden hw


/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:230 memoEI_whnf_sim — **the
`whnf` wrapper**.  Its stuck-tag branch is one rung up: five head kinds, and
the obligation carries `reduceNat = none` and `unfoldDefinition = none` as
well (`whnf_of_stuck`). -/
theorem memoWhnf_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (whnfBody (coreKnot mode fe id fuel) fe) (ConLeche.whnf mode env))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).whnf d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnf mode env) d e s'.store r; ⊤⦄ := by
  rw [coreKnot_whnf_succ]
  sym only [bridge_grind] =>
    vcgen [fun s₁ h1 h2 => hbody s₁ d i e h1 h2 hw] <;> finish

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:283 memoEI_infer_sim — **the
`infer` wrapper**.  Two branches only: inference has no answer-is-the-argument
tag. -/
theorem memoInfer_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (inferBody (coreKnot mode fe id fuel) fe)
      (ConLeche.inferTypeCore mode env))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).infer d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r; ⊤⦄ := by
  rw [coreKnot_infer_succ]
  sym only [bridge_grind] =>
    vcgen [fun s₁ h1 h2 => hbody s₁ d i e h1 h2 hw] <;> finish

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:341 memoEI_inferIO_sim —
**the io wrapper**: the io body under the io grade's OWN table.  A hit here
never serves a full-`infer` query and vice versa — DESIGN §8.3's lesson 9,
which is exactly the fact that the two clauses of `CacheOK` are separate. -/
theorem memoInferIO_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (inferBodyIO (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe)
      (ConLeche.inferTypeIO mode env))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).inferIO d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r; ⊤⦄ := by
  rw [coreKnot_inferIO_succ]
  sym only [bridge_grind] =>
    vcgen [fun s₁ h1 h2 => hbody s₁ d i e h1 h2 hw] <;> finish

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:463 memoBI_defeq_sim — **the
`defeq` wrapper**: two subjects, a `Bool` answer, and the row carries the
verdict so that BOTH SIGNS are sound (DESIGN §8.3's open question, answered by
con-leche's own `defeqC`). -/
theorem memoDefeq_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpecV mode env fe
      (defeqBody mode (coreKnot mode fe id fuel) fe)
      (ConLeche.isDefEqCore mode env))
    (s₀ : AState) (d : Nat) (i j : EIdx) (a b : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store i = some a)
    (hdb : denoteE s₀.store j = some b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).defeq d i j
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV (ConLeche.isDefEqCore mode env) d a b x; ⊤⦄ := by
  rw [coreKnot_defeq_succ]
  -- the spec is instantiated at THIS pair before `vcgen` sees it: `a` and `b`
  -- do not occur in the program, so `vcgen` would leave them as goals, and
  -- with the two `WScoped` hypotheses open an `assumption` can close
  -- `WScoped d ?a` with the WRONG subject, collapsing the two comparands
  -- (DESIGN, task #97-P3-0, rule 4).
  sym only [bridge_grind] =>
    vcgen [fun s₁ h1 h2 h3 => hbody s₁ d i j a b h1 h2 h3 hwa hwb] <;> finish

/-! ## 6. The dispatch step

Every body of the knot opens with `match ← view e with …`.  The body theorems
are proved as a case split on the tag, with one child per group of that
dispatch, and each child starts here: at a state whose store views the
handle as `v`, the program `view i >>= f` is `f v`. -/

/-- con-leche: none — **sequencing at a pinned state**: a triple for `x`
whose postcondition names its facts, and one for the continuation at every
state those facts hold of, make a triple for `x >>= f`.  This is what lets
a long arm be proved stage by stage, each stage's facts introduced by NAME,
instead of as one `vcgen` whose verification conditions carry forty
inaccessible hypotheses. -/
theorem triple_seq {α β : Type} {x : AM α} {f : α → AM β} {s₀ : AState}
    {Q : α → AState → Prop} {R : β → AState → Prop}
    (hx : ⦃fun s => s = s₀⦄ x ⦃fun a s => Q a s; ⊤⦄)
    (hf : ∀ a s₁, Q a s₁ → ⦃fun s => s = s₁⦄ f a ⦃fun b s => R b s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ (x >>= f) ⦃fun b s => R b s; ⊤⦄ := by
  exact Triple.bind x f (fun a s => Q a s) hx fun a =>
    ⟨fun s hs => (hf a s hs).le_wp s rfl⟩


/-- con-leche: none — **the `view` dispatch**: `view i` reads the store and
touches nothing, so a triple for the arm the store selects is a triple for
the whole dispatch.  `view_spec` names the view the store decodes, which is
`v` (`triple_seq`, no verification conditions). -/
theorem view_bind_triple {α : Type} {s₀ : AState} {i : EIdx} {v : ENodeView}
    (hv : s₀.store.view i = some v) {f : ENodeView → AM α}
    {Q : α → AState → Prop}
    (h : ⦃fun s => s = s₀⦄ f v ⦃fun r s' => Q r s'; ⊤⦄) :
    ⦃fun s => s = s₀⦄ (view i >>= f) ⦃fun r s' => Q r s'; ⊤⦄ :=
  triple_seq (view_spec s₀ i) fun _ _ ⟨hs, hv'⟩ => by
    subst hs; cases hv.symm.trans hv'; exact h

/-- con-leche: none — **`view_bind_triple` behind the tag-first twin's test**:
the twin tests the handle's TAG before it reads the node wherever the Rust
does, `if i.tag == t then (view i >>= f) else e`.
At a handle whose view is known the test is decided by the view's own tag
(`EStore.tagOf_of_view`), and on the `else` side the continuation's
catch-all arm IS `e`, so a proof of the view-first form carries over. -/
theorem tag_view_bind_triple {α : Type} {s₀ : AState} {i : EIdx} {v : ENodeView}
    {t : UInt32} (hv : s₀.store.view i = some v) {f : ENodeView → AM α}
    {e : AM α} {Q : α → AState → Prop}
    (h : ⦃fun s => s = s₀⦄ f v ⦃fun r s' => Q r s'; ⊤⦄)
    (he : v.tagOf ≠ t → f v = e) :
    ⦃fun s => s = s₀⦄ (if i.tag == t then (view i >>= f) else e)
      ⦃fun r s' => Q r s'; ⊤⦄ := by
  by_cases ht : (i.tag == t) = true
  · rw [ite_eq_left ht]; exact view_bind_triple hv h
  · rw [ite_eq_right ht, ← he (by rw [← EStore.tagOf_of_view hv]; simpa using ht)]
    exact h

/-- con-leche: none — `tag_view_bind_triple` when the tag test's `else`
branch is NOT the view match's own fallthrough (the `.proj` arm of
a walk whose dangling view and non-constant head fail with different
errors): each branch is given its own triple. -/
theorem tag_view_bind_triple_else {α : Type} {s₀ : AState} {i : EIdx}
    {v : ENodeView} {t : UInt32} (hv : s₀.store.view i = some v)
    {f : ENodeView → AM α} {e : AM α} {Q : α → AState → Prop}
    (h : ⦃fun s => s = s₀⦄ f v ⦃fun r s' => Q r s'; ⊤⦄)
    (he : v.tagOf ≠ t → ⦃fun s => s = s₀⦄ e ⦃fun r s' => Q r s'; ⊤⦄) :
    ⦃fun s => s = s₀⦄ (if i.tag == t then (view i >>= f) else e)
      ⦃fun r s' => Q r s'; ⊤⦄ := by
  by_cases ht : (i.tag == t) = true
  · rw [ite_eq_left ht]; exact view_bind_triple hv h
  · rw [ite_eq_right ht]
    exact he (by rw [← EStore.tagOf_of_view hv]; simpa using ht)

/-- con-leche: none — **the consequence rule at a pinned state**, for the
same reason as `triple_seq`: a callee's published postcondition, read by
name. -/
theorem triple_mono {α : Type} {x : AM α} {s₀ : AState}
    {Q Q' : α → AState → Prop}
    (h : ⦃fun s => s = s₀⦄ x ⦃fun r s => Q r s; ⊤⦄)
    (hq : ∀ r s, Q r s → Q' r s) :
    ⦃fun s => s = s₀⦄ x ⦃fun r s => Q' r s; ⊤⦄ := by
  exact ⟨Triple.entails_wp_of_post h hq⟩


/-- con-leche: none — **a failure claims nothing** (exception postcondition `⊤`), at any pinned
state and any postcondition: every throwing exit of a staged arm is this. -/
theorem triple_fail {α : Type} {s₀ : AState} {e : ConRon.Arena.CheckError}
    {Q : α → AState → Prop} :
    ⦃fun s => s = s₀⦄ (fail e : AM α) ⦃fun r s => Q r s; ⊤⦄ := by
  -- `fail`'s native spec has a schematic postcondition: no verification
  -- condition at all
  vcgen

/-- con-leche: none — the same at the expression store. -/
theorem triple_failDanglingE {α : Type} {s₀ : AState}
    {Q : α → AState → Prop} :
    ⦃fun s => s = s₀⦄ (failDanglingE : AM α) ⦃fun r s => Q r s; ⊤⦄ :=
  triple_fail (Q := Q)


/-! ### The eager slot (con-leche's `withFreshMemos`)

The eager slot runs the eager tower's body under EMPTY mode-dependent memos
and puts the caller's back afterwards.  Its invariant is the state invariant
split along that line: the six entry-point tables are the mode's
(`ModeMemosOK`), everything else in `CheckOK` names no mode.  So the emptied
state is `CheckOK` at ANY mode, in particular the eager tower's, and putting
the caller's tables back — valid at the old store, hence at the grown one —
restores `CheckOK` at the caller's mode. -/

/-- con-leche: ConLeche/Verify/Cached/SimC.lean SimC.freshMemos — the six
mode-dependent tables, valid at `mode` over the store `st`. -/
structure ModeMemosOK (mode : CheckMode) (env : Env) (mm : ModeMemos) (st : EStore) :
    Prop where
  whnfCore : EntryCacheOK (ConLeche.whnfCore mode env) mm.whnfCoreC st
  whnfCoreCheap : EntryCacheOK (fun F d e => ConLeche.whnfCore mode env F d e true)
    mm.whnfCoreCheapC st
  whnf : EntryCacheOK (ConLeche.whnf mode env) mm.whnfC st
  infer : EntryCacheOK (ConLeche.inferTypeCore mode env) mm.inferC st
  inferIO : EntryCacheOK (ConLeche.inferTypeIO mode env) mm.inferIOC st
  defeq : DefeqCacheOK (ConLeche.isDefEqCore mode env) mm.defeqC st

/-- con-leche: none — `ModeMemosOK` transports along the store order. -/
theorem ModeMemosOK.mono {mode : CheckMode} {env : Env} {mm : ModeMemos}
    {st st' : EStore} (h : ModeMemosOK mode env mm st) (hx : Ext st st') :
    ModeMemosOK mode env mm st' :=
  ⟨h.whnfCore.mono hx, h.whnfCoreCheap.mono hx, h.whnf.mono hx, h.infer.mono hx,
    h.inferIO.mono hx, h.defeq.mono hx⟩

/-- con-leche: none — an empty table is valid at any operation. -/
theorem EntryCacheOK.empty {op : Nat → Nat → Expr → CheckM Expr} {st : EStore} :
    EntryCacheOK op ∅ st := fun _ _ h => by simp at h

/-- con-leche: none — an empty verdict table is valid at any operation. -/
theorem DefeqCacheOK.empty {op : Nat → Nat → Expr → Expr → CheckM Bool} {st : EStore} :
    DefeqCacheOK op ∅ st := fun _ _ h => by simp at h

/-- con-leche: ConLeche/Verify/Cached/SimC.lean SimC.freshMemos — **the
detach**: `takeModeMemos` leaves a state that is `CheckOK` at any mode `μ'`
(its six mode-dependent tables are empty, the rest names no mode) and returns
the caller's six tables, valid at the caller's mode. -/
theorem takeModeMemos_ok_spec {mode : CheckMode} {env : Env} {fe : IFEnv}
    (μ' : CheckMode) (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ takeModeMemos
    ⦃fun mm s' => CheckOK μ' env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        ModeMemosOK mode env mm s₀.store; ⊤⦄ := by
  refine triple_mono (takeModeMemos_spec s₀) ?_
  rintro mm s' ⟨rfl, rfl⟩
  have hc := hok.caches
  refine ⟨CheckOK.ofCache hok ⟨EntryCacheOK.empty, EntryCacheOK.empty,
      EntryCacheOK.empty, EntryCacheOK.empty, EntryCacheOK.empty, DefeqCacheOK.empty,
      hc.lvlEq, hc.lvlsEq, hc.constTy, hc.constVal, hc.ruleRhs, hc.readL, hc.readN,
      hc.readLs⟩ rfl rfl, rfl, rfl,
    ⟨hc.whnfCore, hc.whnfCoreCheap, hc.whnf, hc.infer, hc.inferIO, hc.defeq⟩⟩

/-- con-leche: ConLeche/Verify/Cached/SimC.lean SimC.freshMemos — **the
restore**: putting back six tables valid at `mode` over a store the current
one extends gives `CheckOK` at `mode`, whatever mode the current state's own
tables were valid at. -/
theorem putModeMemos_ok_spec {mode μ' : CheckMode} {env : Env} {fe : IFEnv}
    (s₀ : AState) (mm : ModeMemos) {st : EStore} (hok : CheckOK μ' env fe s₀)
    (hm : ModeMemosOK mode env mm st) (hx : Ext st s₀.store) :
    ⦃fun s => s = s₀⦄ putModeMemos mm
    ⦃fun _u s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins; ⊤⦄ := by
  refine triple_mono (putModeMemos_spec s₀ mm) ?_
  rintro _ s' rfl
  have hc := hok.caches
  have hm' := hm.mono hx
  exact ⟨CheckOK.ofCache hok ⟨hm'.whnfCore, hm'.whnfCoreCheap, hm'.whnf, hm'.infer,
      hm'.inferIO, hm'.defeq, hc.lvlEq, hc.lvlsEq, hc.constTy, hc.constVal, hc.ruleRhs,
      hc.readL, hc.readN, hc.readLs⟩ rfl rfl, rfl, rfl⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean ssimC (the `defeqE` slot) —
**the eager slot**: the eager tower's body under fresh mode-dependent memos,
the caller's restored.  Its answer is the eager tower's `isDefEqCore`
(con-leche's `defeqE_def`), and the caller keeps its invariant at its own
mode. -/
theorem memoDefeqE_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat}
    (hbody : BodySpecV mode.toEager env fe
      (defeqBody mode.toEager (coreKnot mode.toEager fe id fuel) fe)
      (ConLeche.isDefEqCore mode.toEager env))
    (s₀ : AState) (d : Nat) (i j : EIdx) (a b : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store i = some a)
    (hdb : denoteE s₀.store j = some b)
    (hwa : Expr.WScoped d a) (hwb : Expr.WScoped d b) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id (fuel + 1)).defeqE d i j
    ⦃fun x s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV (ConLeche.isDefEqCore mode.toEager env) d a b x; ⊤⦄ := by
  rw [coreKnot_defeqE_succ]
  sym only [bridge_grind] =>
    vcgen [takeModeMemos_ok_spec mode.toEager s₀ hok,
      fun s₁ h1 h2 h3 => hbody s₁ d i j a b h1 h2 h3 hwa hwb,
      fun s₂ mm h1 h2 h3 => putModeMemos_ok_spec (mode := mode) (μ' := mode.toEager)
        (env := env) (fe := fe) s₂ mm (st := s₀.store) h1 h2 h3]
      <;> finish

end ConRon.Bridge.Core
