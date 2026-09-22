/-
# `ConRon.Bridge.Core.Memo` — the memo wrappers of the knot's six slots

DESIGN §8.2, and `_tmp/t97/conleche-arena-history.md` §2.3's middle piece:
between the body walks (`Bridge/Core/Arms/*.lean`) and the fuel induction
(`Bridge/Core/Induction.lean`) sit **the memo wrapper steps** — con-leche's
`Verify/Cached/KnotC.lean`, whose six `memoEI_*_sim` / `memoBI_defeq_sim`
theorems are the same six as this module's.

A slot of `Arena/Core.lean`'s `coreKnot` at `fuel + 1` is

```lean
fun d e => do
  if whnfCoreStuckTag e then pure e          -- task #97-P6-7's lever 2
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
  run has to be made depth-universal again.  con-leche's own six
  depth-invariance theorems (`Verify/Deep.lean:3066-3120`) are what does it,
  and they are the reason this module imports con-leche's `Verify` tier at
  all.

## What the cap costs the proof: nothing

`whnfCoreSet` drops the table whole past `cacheCap` (DESIGN §8.3, lesson 10).
The spec below therefore answers with the `if`, and the `CacheOK` insert
lemma takes both branches — because `EntryCacheOK op ∅ st` is vacuously true,
a dropped table is a cache of no rows and satisfies every clause.  This is the
formal content of task #97f's "a dropped row is a cache miss and nothing
else".
-/
import ConRon.Bridge.Core.Knot

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ## 1. The knot's six slots, unfolded once

Task #97-P3-0's rule 9: a definition `mvcgen` would rewrite forever needs its
clauses as lemmas.  `coreKnot` recurses on the fuel, so one `rfl` per slot at
`fuel + 1` unfolds it exactly once — and, because the arena's knot carries its
memo probes INLINE (task #97c's deviation 6), these six equations are also the
only place in the bridge where the probe's shape is written down. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI — the
`whnfCore` slot at `fuel + 1`. -/
theorem coreKnot_whnfCore_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).whnfCore d i =
      (do
        if whnfCoreStuckTag i then pure i
        else
        match (← get).caches.whnfCoreC[i]? with
        | some x => pure x
        | none => do
          let x ← whnfCoreBody mode (coreKnot mode fe id fuel) fe d i
          whnfCoreSet i x
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
          let x ← inferBody mode (coreKnot mode fe id fuel) fe d i
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

/-- con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI — the
`annotate` slot at `fuel + 1`. -/
theorem coreKnot_annotate_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).annotate d i =
      (do
        match (← get).caches.annotC[i]? with
        | some x => pure x
        | none => do
          let x ← annotateBody (coreKnot mode fe id fuel) fe d i
          annotSet i x
          pure x) := rfl

/-- con-leche: ConLeche/Cached/CoreC.lean:1966-1979 coreKnotI — the `inferIO`
slot at `fuel + 1`.  **The mode selects the grade, once per knot level**
(task #97c's smaller deviation 4: the selector is `mode.ioGate`,
`Cached/CoreC.lean:1971`'s spelling, and the two modes agree at `.verified`,
which is where the bridge is stated).  Both arms are written out, so the
equation is `rfl` and the gated arm below is one `if_pos`. -/
theorem coreKnot_inferIO_succ (mode : CheckMode) (fe : IFEnv) (fuel d : Nat)
    (i : EIdx) :
    (coreKnot mode fe id (fuel + 1)).inferIO d i =
      (if mode.ioGate then
        (do
          match (← get).caches.inferIOC[i]? with
          | some x => pure x
          | none => do
            let x ← inferBodyIO mode
              (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d i
            inferIOSet i x
            pure x)
      else
        (do
          match (← get).caches.inferC[i]? with
          | some x => pure x
          | none => do
            let x ← inferBody mode (coreKnot mode fe id fuel) fe d i
            inferSet i x
            pure x)) := rfl

/-! ## 2. The six cache setters' specs

One equation each, and the `if` is the cap's own branch.  Stated as a whole
`AState` equality rather than as a table equation plus thirteen frames: the
setter is one `set` of one record update, so the equation IS the spec and
every frame condition a caller needs falls out of it by `simp`. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `whnfCoreSet`
replaces exactly one field of one record. -/
@[spec] theorem whnfCoreSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ whnfCoreSet e r
    ⦃⇓? _u s' => ⌜s' = { s₀ with caches := { s₀.caches with
        whnfCoreC := (if s₀.caches.whnfCoreC.size < cacheCap then
          s₀.caches.whnfCoreC else ∅).insert e r } }⌝⦄ := by
  mvcgen [whnfCoreSet]
  spec_ro

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `whnfSet`. -/
@[spec] theorem whnfSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ whnfSet e r
    ⦃⇓? _u s' => ⌜s' = { s₀ with caches := { s₀.caches with
        whnfC := (if s₀.caches.whnfC.size < cacheCap then
          s₀.caches.whnfC else ∅).insert e r } }⌝⦄ := by
  mvcgen [whnfSet]
  spec_ro

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `inferSet`. -/
@[spec] theorem inferSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ inferSet e r
    ⦃⇓? _u s' => ⌜s' = { s₀ with caches := { s₀.caches with
        inferC := (if s₀.caches.inferC.size < cacheCap then
          s₀.caches.inferC else ∅).insert e r } }⌝⦄ := by
  mvcgen [inferSet]
  spec_ro

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `inferIOSet`, in
the io grade's own table. -/
@[spec] theorem inferIOSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ inferIOSet e r
    ⦃⇓? _u s' => ⌜s' = { s₀ with caches := { s₀.caches with
        inferIOC := (if s₀.caches.inferIOC.size < cacheCap then
          s₀.caches.inferIOC else ∅).insert e r } }⌝⦄ := by
  mvcgen [inferIOSet]
  spec_ro

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — `annotSet`. -/
@[spec] theorem annotSet_spec (s₀ : AState) (e r : EIdx) :
    ⦃fun s => ⌜s = s₀⌝⦄ annotSet e r
    ⦃⇓? _u s' => ⌜s' = { s₀ with caches := { s₀.caches with
        annotC := (if s₀.caches.annotC.size < cacheCap then
          s₀.caches.annotC else ∅).insert e r } }⌝⦄ := by
  mvcgen [annotSet]
  spec_ro

/-- con-leche: ConLeche/Cached/CoreC.lean:1893-1906 memoBI — `defeqSet`, at
the ORDERED pair and with the verdict. -/
@[spec] theorem defeqSet_spec (s₀ : AState) (a b : EIdx) (r : Bool) :
    ⦃fun s => ⌜s = s₀⌝⦄ defeqSet a b r
    ⦃⇓? _u s' => ⌜s' = { s₀ with caches := { s₀.caches with
        defeqC := (if s₀.caches.defeqC.size < cacheCap then
          s₀.caches.defeqC else ∅).insert (a, b) r } }⌝⦄ := by
  mvcgen [defeqSet]
  spec_ro

/-! ## 3. The cache invariant under an insert

con-leche's `CSOK.insert*` (`Verify/Cached/KnotC.lean:51-174`), with the cap's
`if` taken by the generic lemma so that the six per-table versions are one
line each. -/

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

/-- con-leche: none — a table dropped by the cap holds no row, so it satisfies
every clause: task #97f's "a dropped row is a cache miss and nothing else", as
a lemma. -/
theorem EntryCacheOK.empty {op : Nat → Nat → Expr → CheckM Expr}
    {st : EStore} : EntryCacheOK op (∅ : Std.HashMap EIdx EIdx) st := by
  intro i j hl; simp at hl

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC — the
insert THROUGH the cap's branch, which is the shape the setter's spec
produces. -/
theorem EntryCacheOK.insert_capped {op : Nat → Nat → Expr → CheckM Expr}
    {tbl : Std.HashMap EIdx EIdx} {st : EStore} (h : EntryCacheOK op tbl st)
    {i j : EIdx} {a b : Expr} (ha : denoteE st i = some a)
    (hb : denoteE st j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true → op F d a = .ok b) :
    EntryCacheOK op
      ((if tbl.size < cacheCap then tbl else ∅).insert i j) st := by
  split
  · exact EntryCacheOK.insert h ha hb hrun
  · exact EntryCacheOK.insert EntryCacheOK.empty ha hb hrun

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:146 CSOK.insertDefeqC — the
`defeq` verdict cache's insert, BOTH SIGNS (the row carries the `Bool` the
pure run answered). -/
theorem DefeqCacheOK.insert_capped {op : Nat → Nat → Expr → Expr → CheckM Bool}
    {tbl : Std.HashMap (EIdx × EIdx) Bool} {st : EStore}
    (h : DefeqCacheOK op tbl st) {i j : EIdx} {a b : Expr} {x : Bool}
    (ha : denoteE st i = some a) (hb : denoteE st j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true → Expr.wscopedB d b = true →
      op F d a b = .ok x) :
    DefeqCacheOK op
      ((if tbl.size < cacheCap then tbl else ∅).insert (i, j) x) st := by
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
  split
  · exact key _ h
  · exact key _ (by intro k r hl; simp at hl)

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
      whnfCoreC := (if s.caches.whnfCoreC.size < cacheCap then
        s.caches.whnfCoreC else ∅).insert i j } } :=
  { hc with whnfCore := EntryCacheOK.insert_capped hc.whnfCore ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:69 CSOK.insertWhnfC. -/
theorem CacheOK.insertWhnf {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.whnf mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      whnfC := (if s.caches.whnfC.size < cacheCap then
        s.caches.whnfC else ∅).insert i j } } :=
  { hc with whnf := EntryCacheOK.insert_capped hc.whnf ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:87 CSOK.insertInferC. -/
theorem CacheOK.insertInfer {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.inferTypeCore mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      inferC := (if s.caches.inferC.size < cacheCap then
        s.caches.inferC else ∅).insert i j } } :=
  { hc with infer := EntryCacheOK.insert_capped hc.infer ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:108 CSOK.insertInferIOC. -/
theorem CacheOK.insertInferIO {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.inferTypeIO mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      inferIOC := (if s.caches.inferIOC.size < cacheCap then
        s.caches.inferIOC else ∅).insert i j } } :=
  { hc with inferIO := EntryCacheOK.insert_capped hc.inferIO ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:127 CSOK.insertAnnotC. -/
theorem CacheOK.insertAnnot {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true →
      ConLeche.annotateCore mode env F d a = .ok b) :
    CacheOK mode env { s with caches := { s.caches with
      annotC := (if s.caches.annotC.size < cacheCap then
        s.caches.annotC else ∅).insert i j } } :=
  { hc with annot := EntryCacheOK.insert_capped hc.annot ha hb hrun }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:146 CSOK.insertDefeqC. -/
theorem CacheOK.insertDefeq {mode : CheckMode} {env : Env} {s : AState}
    (hc : CacheOK mode env s) {i j : EIdx} {a b : Expr} {x : Bool}
    (ha : denoteE s.store i = some a) (hb : denoteE s.store j = some b)
    (hrun : ∃ F, ∀ d, Expr.wscopedB d a = true → Expr.wscopedB d b = true →
      ConLeche.isDefEqCore mode env F d a b = .ok x) :
    CacheOK mode env { s with caches := { s.caches with
      defeqC := (if s.caches.defeqC.size < cacheCap then
        s.caches.defeqC else ∅).insert (i, j) x } } :=
  { hc with defeq := DefeqCacheOK.insert_capped hc.defeq ha hb hrun }

/-! ### `CheckOK` past a cache insert

The store, the pins and the environment index do not move, so the whole
invariant follows from the cache clause alone. -/

/-- con-leche: none — `CheckOK` from `CacheOK` at a state whose store, pins
and index are the old ones. -/
theorem CheckOK.ofCache {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK mode env fe s) (hc : CacheOK mode env s')
    (hst : s'.store = s.store) (hp : s'.pins = s.pins) :
    CheckOK mode env fe s' where
  state := ⟨hst ▸ h.state.wf⟩
  caches := hc
  pins := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hst, hp] <;>
      first
        | exact h.pins.ready | exact h.pins.names | exact h.pins.reserved
        | exact h.pins.emptyLevels | exact h.pins.zeroLevel
        | exact h.pins.sortOne
  ienv := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [hst]
    · exact h.ienv.hit
    · exact h.ienv.cover
    · exact h.ienv.proj


/-! ## 4. The stuck-tag branch (task #97-P6-7's lever 2)

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
      (∃ l, e = .lit l) ∨ (∃ t b m, e = .lam t b m) ∨
      (∃ t b m, e = .forallE t b m) := by
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
  | lam ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hv he
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨et, eb, m, rfl⟩))))
  | forallE ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv he
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨et, eb, m, rfl⟩))))
  | letE ty w b => exact absurd (htag.trans rfl) hlet
  | lit l =>
    rw [denote_lit_inv hwf hv he]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨l, rfl⟩)))
  | proj n i sub => exact absurd (htag.trans rfl) hproj

/-- con-leche: ConLeche/Kernel/Core.lean:968-975 whnfCoreBody — the six
constructors the body's first six clauses answer with themselves. -/
theorem whnfCore_of_stuck {mode : CheckMode} {env : Env} {e : Expr}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l) ∨
      (∃ t b m, e = .lam t b m) ∨ (∃ t b m, e = .forallE t b m))
    (F d : Nat) : ConLeche.whnfCore mode env (F + 1) d e = .ok e := by
  rw [ConLeche.whnfCore_succ]
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ |
      ⟨t, b, m, rfl⟩ | ⟨t, b, m, rfl⟩ <;>
    simp [ConLeche.whnfCoreBody, pure, Except.pure]


/-- con-leche: ConLeche/Kernel/Core.lean:1097-1099 whnfBody — the same at the
reduction loop: a handle whose tag is `sort`, `fvar`, `lam`, `forallE` or
`lit` denotes one of those five. -/
theorem denote_stuck_of_whnfStuckTag {st : EStore} (hwf : StoreWF st)
    {h : EIdx} {e : Expr} (he : denoteE st h = some e)
    (hs : whnfStuckTag h = true) :
    (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨ (∃ t b m, e = .lam t b m) ∨
      (∃ t b m, e = .forallE t b m) ∨ (∃ l, e = .lit l) := by
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
  | lam ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_lam_inv hwf hv he
    exact Or.inr (Or.inr (Or.inl ⟨et, eb, m, rfl⟩))
  | forallE ty b m =>
    obtain ⟨et, eb, rfl, _, _⟩ := denote_forallE_inv hwf hv he
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨et, eb, m, rfl⟩)))
  | letE ty w b => rw [htag] at htg; simp [ENodeView.tagOf, ETag.letE,
      ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit] at htg
  | lit l =>
    rw [denote_lit_inv hwf hv he]
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩)))
  | proj n i sub => rw [htag] at htg; simp [ENodeView.tagOf, ETag.proj,
      ETag.sort, ETag.fvar, ETag.lam, ETag.forallE, ETag.lit] at htg

/-- con-leche: ConLeche/Kernel/Core.lean:1073-1099 whnfStep/whnfBody — the
five constructors the reduction loop cannot move: `whnfCore` returns them
unchanged, `reduceNat`'s match needs an `.app` and `unfoldDefinition`'s needs
a `.const` head, so the first iteration of the loop is `pure e`.  **Two fuel
levels**, because the loop's own `whnfCore` call consumes one. -/
theorem whnf_of_stuck {mode : CheckMode} {env : Env} {e : Expr}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ t b m, e = .lam t b m) ∨ (∃ t b m, e = .forallE t b m) ∨
      (∃ l, e = .lit l))
    (F d : Nat) : ConLeche.whnf mode env (F + 2) d e = .ok e := by
  obtain ⟨n, hn⟩ := ConLeche.whnfLoopFuel_succ
  rw [show F + 2 = (F + 1) + 1 from rfl, ConLeche.whnf_succ,
    ConLeche.whnfBody, hn, ConLeche.whnfLoop, ConLeche.whnfStep]
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨t, b, m, rfl⟩ | ⟨t, b, m, rfl⟩ |
      ⟨l, rfl⟩ <;>
    simp [ConLeche.pureFns_whnfCore, ConLeche.whnfCoreBody, ConLeche.reduceNat,
      ConLeche.unfoldDefinition, ConLeche.Expr.getAppFn, pure, Except.pure,
      bind, Except.bind]


/-! ## 5. The six memo-wrapper steps

con-leche's `Verify/Cached/KnotC.lean:175-529`, one per slot: from the body
walk at fuel `f`, the SLOT at fuel `f + 1`. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:175 memoEI_whnfCore_sim —
**the `whnfCore` wrapper**: stuck tag, cache hit, cache miss. -/
theorem memoWhnfCore_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (whnfCoreBody mode (coreKnot mode fe id fuel) fe)
      (ConLeche.whnfCore mode env))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id (fuel + 1)).whnfCore d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnfCore mode env) d e s'.store r⌝⦄ := by
  rw [coreKnot_whnfCore_succ]
  have hb := hbody
  simp only [BodySpec] at hb
  mvcgen [hb]
  -- **the stuck tag**: neither the store nor the memo is touched, and the
  -- pure body answers with its own argument
  · rename_i hs _ hst
    subst hst
    exact ⟨hok, Ext.refl _, rfl, e, hden, hw, 1,
      whnfCore_of_stuck
        (denote_stuck_of_whnfCoreStuckTag hok.state.wf hden hs) 0 d⟩
  -- **the hit**: `CacheOK`'s depth-universal row, consumed at the query's
  -- own depth (the history report's lesson 8)
  · rename_i _ _ hst x hx
    subst hst
    obtain ⟨a, b, ha, hb', F, hall⟩ := hok.caches.whnfCore i x hx
    rw [hden] at ha
    obtain rfl := Option.some.inj ha
    have hrun := hall d hw.to_wscopedB
    exact ⟨hok, Ext.refl _, rfl, b, hb',
      ConLeche.whnfCore_WScoped henv F hrun hw, F, hrun⟩
  -- the body call's two preconditions
  · rename_i _ _ hst _; subst hst; exact hok
  · rename_i _ _ hst _; subst hst; exact hden
  -- **the miss**: the body's answer, re-inserted in the depth-universal form
  · rename_i _ _ hst2 _ r s1 hpost _ _ hst3
    subst hst3
    subst hst2
    obtain ⟨hck, hx, hpn, v, hv, hwv, F, hF⟩ := hpost
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertWhnfCore hck.caches (denote_ext hden hx) hv
          ⟨F, fun d' hd' => by
            rw [ConLeche.whnfCore_depth_inv henv F hd' hw.to_wscopedB]
            exact hF⟩) rfl rfl,
      hx, hpn, v, hv, hwv, F, hF⟩


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
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id (fuel + 1)).whnf d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.whnf mode env) d e s'.store r⌝⦄ := by
  rw [coreKnot_whnf_succ]
  have hb := hbody
  simp only [BodySpec] at hb
  mvcgen [hb]
  · rename_i hs _ hst
    subst hst
    exact ⟨hok, Ext.refl _, rfl, e, hden, hw, 2,
      whnf_of_stuck (denote_stuck_of_whnfStuckTag hok.state.wf hden hs) 0 d⟩
  · rename_i _ _ hst x hx
    subst hst
    obtain ⟨a, b, ha, hb', F, hall⟩ := hok.caches.whnf i x hx
    rw [hden] at ha
    obtain rfl := Option.some.inj ha
    have hrun := hall d hw.to_wscopedB
    exact ⟨hok, Ext.refl _, rfl, b, hb',
      ConLeche.whnf_WScoped henv F hrun hw, F, hrun⟩
  · rename_i _ _ hst _; subst hst; exact hok
  · rename_i _ _ hst _; subst hst; exact hden
  · rename_i _ _ hst2 _ r s1 hpost _ _ hst3
    subst hst3
    subst hst2
    obtain ⟨hck, hx, hpn, v, hv, hwv, F, hF⟩ := hpost
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertWhnf hck.caches (denote_ext hden hx) hv
          ⟨F, fun d' hd' => by
            rw [ConLeche.whnf_depth_inv henv F hd' hw.to_wscopedB]
            exact hF⟩) rfl rfl,
      hx, hpn, v, hv, hwv, F, hF⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:283 memoEI_infer_sim — **the
`infer` wrapper**.  Two branches only: inference has no answer-is-the-argument
tag. -/
theorem memoInfer_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (inferBody mode (coreKnot mode fe id fuel) fe)
      (ConLeche.inferTypeCore mode env))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id (fuel + 1)).infer d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeCore mode env) d e s'.store r⌝⦄ := by
  rw [coreKnot_infer_succ]
  have hb := hbody
  simp only [BodySpec] at hb
  mvcgen [hb]
  · rename_i _ hst x hx
    subst hst
    obtain ⟨a, b, ha, hb', F, hall⟩ := hok.caches.infer i x hx
    rw [hden] at ha
    obtain rfl := Option.some.inj ha
    have hrun := hall d hw.to_wscopedB
    exact ⟨hok, Ext.refl _, rfl, b, hb',
      ConLeche.inferTypeCore_WScoped henv F hrun hw, F, hrun⟩
  · rename_i _ hst _; subst hst; exact hok
  · rename_i _ hst _; subst hst; exact hden
  · rename_i _ hst2 _ r s1 hpost _ _ hst3
    subst hst3
    subst hst2
    obtain ⟨hck, hx, hpn, v, hv, hwv, F, hF⟩ := hpost
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertInfer hck.caches (denote_ext hden hx) hv
          ⟨F, fun d' hd' => by
            rw [ConLeche.inferTypeCore_depth_inv henv F hd' hw.to_wscopedB]
            exact hF⟩) rfl rfl,
      hx, hpn, v, hv, hwv, F, hF⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:408 memoEI_annotate_sim —
**the `annotate` wrapper**. -/
theorem memoAnnotate_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hbody : BodySpec mode env fe
      (annotateBody (coreKnot mode fe id fuel) fe)
      (ConLeche.annotateCore mode env))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id (fuel + 1)).annotate d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.annotateCore mode env) d e s'.store r⌝⦄ := by
  rw [coreKnot_annotate_succ]
  have hb := hbody
  simp only [BodySpec] at hb
  mvcgen [hb]
  · rename_i _ hst x hx
    subst hst
    obtain ⟨a, b, ha, hb', F, hall⟩ := hok.caches.annot i x hx
    rw [hden] at ha
    obtain rfl := Option.some.inj ha
    have hrun := hall d hw.to_wscopedB
    exact ⟨hok, Ext.refl _, rfl, b, hb',
      ConLeche.annotateCore_WScoped F _ hrun hw, F, hrun⟩
  · rename_i _ hst _; subst hst; exact hok
  · rename_i _ hst _; subst hst; exact hden
  · rename_i _ hst2 _ r s1 hpost _ _ hst3
    subst hst3
    subst hst2
    obtain ⟨hck, hx, hpn, v, hv, hwv, F, hF⟩ := hpost
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertAnnot hck.caches (denote_ext hden hx) hv
          ⟨F, fun d' hd' => by
            rw [ConLeche.annotateCore_depth_inv henv F hd' hw.to_wscopedB]
            exact hF⟩) rfl rfl,
      hx, hpn, v, hv, hwv, F, hF⟩

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:341 memoEI_inferIO_sim —
**the io wrapper**, at the gated mode (`mode.ioGate = true`, which every
verified mode is): the io body under the io grade's OWN table.  A hit here
never serves a full-`infer` query and vice versa — DESIGN §8.3's lesson 9,
which is exactly the fact that the two clauses of `CacheOK` are separate. -/
theorem memoInferIO_step {mode : CheckMode} {env : Env} {fe : IFEnv}
    {fuel : Nat} (henv : ConLeche.EnvWF env) (hg : mode.ioGate = true)
    (hbody : BodySpec mode env fe
      (inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe)
      (ConLeche.inferTypeIO mode env))
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id (fuel + 1)).inferIO d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimE (ConLeche.inferTypeIO mode env) d e s'.store r⌝⦄ := by
  rw [coreKnot_inferIO_succ, if_pos hg]
  have hb := hbody
  simp only [BodySpec] at hb
  mvcgen [hb]
  · rename_i _ hst x hx
    subst hst
    obtain ⟨a, b, ha, hb', F, hall⟩ := hok.caches.inferIO i x hx
    rw [hden] at ha
    obtain rfl := Option.some.inj ha
    have hrun := hall d hw.to_wscopedB
    exact ⟨hok, Ext.refl _, rfl, b, hb',
      ConLeche.inferTypeIO_WScoped henv F hrun hw, F, hrun⟩
  · rename_i _ hst _; subst hst; exact hok
  · rename_i _ hst _; subst hst; exact hden
  · rename_i _ hst2 _ r s1 hpost _ _ hst3
    subst hst3
    subst hst2
    obtain ⟨hck, hx, hpn, v, hv, hwv, F, hF⟩ := hpost
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertInferIO hck.caches (denote_ext hden hx) hv
          ⟨F, fun d' hd' => by
            rw [ConLeche.inferTypeIO_depth_inv henv F hd' hw.to_wscopedB]
            exact hF⟩) rfl rfl,
      hx, hpn, v, hv, hwv, F, hF⟩

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
    ⦃fun s => ⌜s = s₀⌝⦄ (coreKnot mode fe id (fuel + 1)).defeq d i j
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimV (ConLeche.isDefEqCore mode env) d a b x⌝⦄ := by
  rw [coreKnot_defeq_succ]
  -- the spec is instantiated at THIS pair before `mvcgen` sees it: with the
  -- two `WScoped` hypotheses still open, `assumption` closes `WScoped d ?a`
  -- with the WRONG subject and the two comparands collapse (measured).
  -- Task #97-P3-0's rule 4 at a second subject.
  have hb : ∀ (s₁ : AState), CheckOK mode env fe s₁ →
      denoteE s₁.store i = some a → denoteE s₁.store j = some b →
      ⦃fun s => ⌜s = s₁⌝⦄ defeqBody mode (coreKnot mode fe id fuel) fe d i j
      ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₁.store s'.store ∧
          s'.pins = s₁.pins ∧
          SimV (ConLeche.isDefEqCore mode env) d a b x⌝⦄ :=
    fun s₁ h1 h2 h3 => hbody s₁ d i j a b h1 h2 h3 hwa hwb
  mvcgen [hb]
  · rename_i _ hst x hx
    subst hst
    obtain ⟨a', b', ha', hb', F, hall⟩ := hok.caches.defeq (i, j) x hx
    rw [hda] at ha'
    rw [hdb] at hb'
    obtain rfl := Option.some.inj ha'
    obtain rfl := Option.some.inj hb'
    exact ⟨hok, Ext.refl _, rfl, F, hall d hwa.to_wscopedB hwb.to_wscopedB⟩
  · rename_i _ hst _; subst hst; exact hok
  · rename_i _ hst _; subst hst; exact hda
  · rename_i _ hst _; subst hst; exact hdb
  · rename_i _ hst2 _ r s1 hpost _ _ hst3
    subst hst3
    subst hst2
    obtain ⟨hck, hx, hpn, F, hF⟩ := hpost
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertDefeq hck.caches (denote_ext hda hx) (denote_ext hdb hx)
          ⟨F, fun d' hda' hdb' => by
            rw [ConLeche.isDefEqCore_depth_inv henv F hda' hdb'
              hwa.to_wscopedB hwb.to_wscopedB]
            exact hF⟩) rfl rfl,
      hx, hpn, F, hF⟩

end ConRon.Bridge.Core
