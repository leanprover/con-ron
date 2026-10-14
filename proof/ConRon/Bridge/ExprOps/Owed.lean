/-
# `ConRon.Bridge.ExprOps.Owed` — the five twins the earlier round only stated

DESIGN §8.2's Theorem 1 for the five twins of `Arena/ExprOps.lean` whose
STATEMENT an earlier round owed and whose PROOF it did not reach (task
#97-P3-2): three `…Fast` entry brackets and the two walks whose fuel
induction the round ran out on —

* `abstract1Fast` and `abstractRangeFast`, the two brackets over the EXECUTED
  abstraction walks, and `abstractRangeGo` itself;
* `instLPGo` and `instLPFast`.

`Bridge/ExprOps/{Abs,InstLP,MemoSpecs}.lean` carry the vocabulary and the
callee specs each of them consumes; what is added here is the two `…Spec`
records the two walks are inducted over (`AbsRangeGoSpec`, `InstLPSpec`),
`instLPGo`'s pure function as a named term with its equations (`instLPFn`),
the `grind` vocabulary the level arms need, and three pieces of arena/spec
infrastructure that belong further down the stack and are flagged in place
(`view_eq_viewAt`, `readNameM_specF` / `readNamesM_specF`).

## The closer (task #123)

Every walk is `sym only [bridge_grind, …] => vcgen [...] <;> finish`, as in
`ExprOps/Abs.lean` (whose header says what `grind` is given): the two walks
here are not split into arm theorems — `vcgen` unfolds the arms in place —
and the entries convert the named function back to the statement's `fun`
by unfolding it (`abs1Fn`, `absRangeFn`, `instLPFn` in the `sym` list).

## The deviations each statement carries

The ones `Arena/ExprOps.lean`'s own doc comments name:

* `abstractRangeGo` / `abstractRangeFast` are the EXECUTED form and
  `abstractRange` (proved in `Abs.lean`) is the SPEC descent — task
  #97-P6-11's clause change, whose equations are `Abs.lean`'s
  `abstractRange_zero_eq` and `abstractRange_of_fvarRange_le`.  Both call
  `fvarB` before they read the store, so both carry `Abs.lean`'s `FvarBSpec`
  as a hypothesis (this module does not import `ExprOps/Ranges.lean` and
  cannot discharge it);
* `instLPGo`'s `ks`/`us` are TRANSIENT `List Name` / `List Level` (DESIGN
  §8.3 lesson 4), so `instLPFast`'s theorem carries the readback hypotheses
  its entry establishes with `readNamesM` / `readLevelsM`.

## Three statement changes this round had to make

The shapes the earlier round wrote down were not provable, and the reasons are
worth keeping:

1. **`abstractRangeGo_specS`'s memo invariant is `AbsRangeMemoA d k`, not
   `Abs1MemoA d`.**  The table `abs1C` is shared by the two abstraction walks
   (`Arena/ExprOps.lean`: "That is a table IDENTITY, not a clause"), and what
   it holds inside an `abstractRangeFast` call is `abstractRange` answers.
   `Abs1MemoA d` is the `abstract1` reading and is false of this walk for
   every `k ≠ 1`.
2. **`abstractRangeFast_spec`'s and `instLPFast_spec`'s memo clause is a
   DISJUNCTION**, `s'.memos.xC = ∅ ∨ s' = s₀`, where `abstract1Fast_spec`
   carries the equation.  Both of these entries test their cutoff FIRST and
   return the subject without clearing anything — `abstractRangeFast` at
   `k = 0` (task #97-P6-11) and `instLPFast` at `hasLP = false` (the cutoff
   hoisted over the readbacks, task #97-P6-10).  The second disjunct is the
   stronger of the two for a caller: nothing moved at all.
3. **`instLPGo_specS` and `instLPFast_spec` frame `s'.caches` as a RECORD
   EQUATION** (round 4; the earlier rounds did not frame it at all).
   `ExprOps/InstLP.lean`'s header says why it cannot be `s'.caches =
   s₀.caches`: the two LEVEL arms read a level back and the memoised readback
   WRITES `caches.readLC` / `caches.readLsC`, and `instLPFast`'s entry writes
   `caches.readNC` as well.  What both carry is

       s'.caches = { s₀.caches with readLC := …, readNC := …, readLsC := … }

   — `readLevelM_spec`'s own spelling (`Bridge/Specs.lean`: *"a record
   EQUATION and not a table equation"*), naming only the tables the call
   actually moves and framing the other eleven in one line.  With it
   `ReadNCacheOK s'.caches.readNC s'.store` is a conjunct too, because the
   name-readback cache is framed across `instLPGo` and `ReadNCacheOK.mono`
   carries the clause along the walk's `Ext`.

   **What it cost**: the same record equation stated one level down at each
   of `readNameM_specF`, `readNamesM_specF` (this file),
   `readLevelM_specF`, `readLevelsM_specF` (`ExprOps/MemoSpecs.lean`) and
   `substLMemoAt_spec`, `substLsMemoAt_spec` (`ExprOps/InstLP.lean`) — each
   replacing the two sibling-table equations it used to carry, which are its
   projections — and **one lemma in `instLPFast_spec`'s closer list**
   (`ReadNCacheOK.mono`).  Every other proof of the chain closed unchanged.
   `instLPGo_specS`'s fourteen structural blocks each gained one `by grind` /
   one `rfl`.
-/
import ConRon.Bridge.ExprOps.Abs
import ConRon.Bridge.ExprOps.MemoSpecs
import ConRon.Bridge.ExprOps.InstLP
import ConRon.Bridge.SpecsL

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 4000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ### Attribute hygiene

`ExprOps/MemoSpecs.lean`'s `internRebuiltBind_specV` — the binder intern with
the view-monotonicity conjunct — is tagged `@[local spec high]` in
`ExprOps/Abs.lean`, and a LOCAL attribute does not travel through an
import.  The executed `abstractRange` walk below needs it for exactly the
reason the executed `abstract1` walk does, so this file repeats the line. -/
attribute [local spec high] internRebuiltBind_specV


/-! ## `abstract1`'s entry -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1930-1932 abstract1Fast — the
bracket over `abstract1Go_spec`, whose shape is `ExprOps/Inst1.lean`'s
`instantiate1Fast_spec`: the memo is cleared before and after, and the cleared
memo satisfies `Abs1MemoA` for free (`MemoOK.of_empty`).  `hfv` is the
`fvarB` assumption `abstract1Go_spec` takes and this module cannot discharge
(it does not import `ExprOps/Ranges.lean`). -/
theorem abstract1Fast_spec (hfv : FvarBSpec) (fuel : Nat) (s₀ : AState)
    (e : EIdx) (d k : Nat)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ abstract1Fast fuel e d k
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.abs1C = ∅ ∧
        RelE (fun x => Expr.abstract1 x d k) s₀.store e s'.store r; ⊤⦄ := by
  sym only [bridge_grind, abs1Fn, MemoOK.of_empty] =>
    vcgen [abstract1Fast, (abstract1Go_spec hfv d fuel).run] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-811 abstractRange —
Theorem 1's statement for one level of the EXECUTED descent's recursion.
The memo invariant is `AbsRangeMemoA d k` and NOT `Abs1MemoA d`: the table
`abs1C` is shared by the two walks, and what it holds inside an
`abstractRangeFast` call is `abstractRange` answers (`Arena/ExprOps.lean`'s
"That is a table IDENTITY, not a clause"). -/
structure AbsRangeGoSpec (d k : Nat) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx) (c : Nat), StateOK s₁ →
    AbsRangeMemoA d k s₁ → (denoteE s₁.store h).isSome = true →
    ⦃fun s => s = s₁⦄ rec h c
    ⦃fun r s' => StateOK s' ∧ AbsRangeMemoA d k s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        AbsRangeAt d k c s₁.store h s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-811 abstractRange —
**THEOREM 1 for the EXECUTED `abstractRange`**, at one level of the
recursion, by induction on the fuel.  `abstract1Go_spec`'s shape with the
five arms unfolded in place (they are not split into theorems of their own):
the `fvarB` cutoff (`absRangeFn_cutoff`), the tag chain, the catch-all
(`absRangeFn_leaf`). -/
theorem abstractRangeGo_specS (hfv : FvarBSpec) (d k : Nat) :
    ∀ fuel, AbsRangeGoSpec d k (abstractRangeGo d k fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h c _ _ _
    sym only [bridge_grind] => vcgen [abstractRangeGo_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h c hok hm hden
    sym only [bridge_grind, denoteEView, opt2, opt3, ETag.isBind, absRangeFn_cutoff,
        absRangeFn_leaf] =>
      vcgen [abstractRangeGo_succ, absRangeGoArmApp, absRangeGoArmBind,
        absRangeArmFVar, absRangeGoArmLet, absRangeGoArmProj, ih.run, hfv.run,
        abs1Set_specA (f := absRangeFn d k)] <;> finish (gen := 10)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:748-755 abstractRangeC — the
bracket over `abstractRangeGo_specS`.

**The memo clause is a DISJUNCTION here and an equation at the other four
entries** (a statement change this round had to make: the shape the round
owed was not provable).  `abstractRangeFast` tests `k = 0` FIRST and returns
the subject without clearing anything (`Arena/ExprOps.lean`'s own clause, and
what makes the annotation telescope's outermost binder domain cost nothing),
so on that branch the shared `abs1C` table is whatever the caller had.  What
is true of BOTH branches is "either the table was dropped or nothing moved at
all", and the second disjunct is the stronger of the two for a caller. -/
theorem abstractRangeFast_spec (hfv : FvarBSpec) (fuel : Nat) (s₀ : AState)
    (e : EIdx) (d k c : Nat) (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ abstractRangeFast fuel e d k c
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (s'.memos.abs1C = ∅ ∨ s' = s₀) ∧
        RelE (fun x => Expr.abstractRange x d k c) s₀.store e s'.store r; ⊤⦄ := by
  sym only [bridge_grind, absRangeFn, MemoOK.of_empty, abstractRange_zero_eq] =>
    vcgen [abstractRangeFast, (abstractRangeGo_specS hfv d k fuel).run] <;> finish

/-! ## `instantiateLevelParams`' entry -/

/-! ### The pure function, named, and its equations

As `ExprOps/Abs.lean`'s `abs1Fn`: the walk's function is a TERM, not a
`fun`, so that `grind` sees the answer relation and the memo invariant as
atoms.  The memo table is keyed `(h, 0)`, so the function takes the (unused)
cursor first, which makes `instLPFn ks us` the memo invariant's function and
`instLPFn ks us 0` the answer relation's. -/

/-- con-leche: ConLeche/Kernel/Level.lean:234-249 Expr.instantiateLevelParams —
with the memo key's (unused) cursor first. -/
def instLPFn (ks : List ConLeche.Name) (us : List Level) (_c : Nat) (e : Expr) : Expr :=
  e.instantiateLevelParams ks us

section
variable (ks : List ConLeche.Name) (us : List Level) (c : Nat)

/-- con-leche: ConLeche/Kernel/Level.lean:235 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_bvar (i : Nat) : instLPFn ks us c (.bvar i) = .bvar i := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:236 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_fvar (i : Nat) (t : Expr) :
    instLPFn ks us c (.fvar i t) = .fvar i (instLPFn ks us c t) := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:237 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_sort (u : Level) :
    instLPFn ks us c (.sort u) = .sort (Level.subst ks us u) := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:238 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_const (n : ConLeche.Name) (vs : List Level) :
    instLPFn ks us c (.const n vs) = .const n (vs.map (Level.subst ks us)) := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:239 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_app (f a : Expr) :
    instLPFn ks us c (.app f a) = .app (instLPFn ks us c f) (instLPFn ks us c a) := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:240-242 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_lam (t b : Expr) :
    instLPFn ks us c (.lam t b) = .lam (instLPFn ks us c t) (instLPFn ks us c b) := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:243-245 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_forallE (t b : Expr) :
    instLPFn ks us c (.forallE t b) = .forallE (instLPFn ks us c t) (instLPFn ks us c b) :=
  rfl
/-- con-leche: ConLeche/Kernel/Level.lean:246-247 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_letE (t w b : Expr) :
    instLPFn ks us c (.letE t w b) =
      .letE (instLPFn ks us c t) (instLPFn ks us c w) (instLPFn ks us c b) := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:248 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_lit (l : Literal) : instLPFn ks us c (.lit l) = .lit l := rfl
/-- con-leche: ConLeche/Kernel/Level.lean:249 Expr.instantiateLevelParams. -/
@[bridge_grind =] theorem instLPFn_proj (n : ConLeche.Name) (i : Nat) (s : Expr) :
    instLPFn ks us c (.proj n i s) = .proj n i (instLPFn ks us c s) := rfl

end

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2242
Expr.instantiateLevelParams_eq_self — **the `hasLP` cutoff's licence**: a
term with no level parameter is its own instantiation. -/
theorem instLPFn_cutoff {ks : List ConLeche.Name} {us : List Level} {c : Nat} {e : Expr}
    (h : e.hasLevelParam = false) : instLPFn ks us c e = e :=
  Expr.instantiateLevelParams_eq_self h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2541 Expr.hasLP_eq — the packed
`hasLP` bit the arena reads IS the denotation's `hasLevelParam`
(`EStore.derived_exact`), keyed by the derived-word read and the
denotation. -/
theorem lpOfData_derived {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) : lpOfData (st.derived h) = e.hasLevelParam := by
  rw [EStore.derived_exact hwf he]; exact Expr.Expr.hasLP_eq e
grind_pattern [bridge_grind] lpOfData_derived => st.derived h, some e where
  guard denoteE st h = some e

/-! ### The answer relation and the memo invariant -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiateLevelParams`'
answer relation. -/
abbrev InstLPAt (ks : List ConLeche.Name) (us : List Level) :
    EStore → EIdx → EStore → EIdx → Prop :=
  RelE (instLPFn ks us 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2546-2550 InstLPMemoInv — the
expression memo's invariant at the named function (`Bridge/StateOK.lean`'s
`InstLPMemoA` with a `fun`, definitionally). -/
abbrev InstLPMemoF (ks : List ConLeche.Name) (us : List Level) (s : AState) : Prop :=
  MemoOK (instLPFn ks us) s.memos.instLPC s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2546-2550 InstLPMemoInv — `instLPSet`
carrying the memo invariant of the walk `f` the caller names
(`ExprOps/Abs.lean`'s `abs1Set_specA`). -/
theorem instLPSet_specA (f : Nat → Expr → Expr) (s₀ : AState) (h : EIdx) (c : Nat)
    (r : EIdx) (hk : (denoteE s₀.store h).isSome = true)
    (hm : MemoOK f s₀.memos.instLPC s₀.store) (hr : RelE (f c) s₀.store h s₀.store r) :
    ⦃fun s => s = s₀⦄ instLPSet (h, c) r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos.instLPLC = s₀.memos.instLPLC ∧
        s'.memos.instLPLsC = s₀.memos.instLPLsC ∧
        MemoOK f s'.memos.instLPC s'.store; ⊤⦄ := by
  vcgen [instLPSet]
  subst_vars
  exact ⟨rfl, rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

/-! ### Vocabulary candidates for Bridge/Grind.lean (task #123)

The level answers and the remaining view constructors, in
`ExprOps/Abs.lean`'s style. -/

/-- con-leche: none — `RelL`/`RelLs`'s answer at an optional subject (`MapRel`
at any carrier). -/
def MapRelG {α β : Type} (g : α → β) : Option α → Option β → Prop
  | some a, o => o = some (g a)
  | none, _ => True

/-- con-leche: none — `MapRelG` at a present subject. -/
@[bridge_grind =] theorem MapRelG.some_eq {α β : Type} (g : α → β) (a : α) (o : Option β) :
    MapRelG g (some a) o = (o = some (g a)) := rfl

/-- con-leche: none — `RelL` IS a `MapRelG` fact on the two level
denotations. -/
@[bridge_grind =] theorem RelL_eq_mapRelG (g : Level → Level) (st : EStore) (c : LIdx)
    (st' : EStore) (r : LIdx) :
    RelL g st c st' r = MapRelG g (denoteL st.ls c) (denoteL st'.ls r) := by
  apply propext; constructor
  · intro h; cases hc : denoteL st.ls c with
    | none => trivial
    | some u => exact h u hc
  · intro h u hu; rw [hu] at h; exact h

/-- con-leche: none — `RelLs` IS a `MapRelG` fact on the two level-list
denotations. -/
@[bridge_grind =] theorem RelLs_eq_mapRelG (g : List Level → List Level) (st : EStore)
    (c : LsIdx) (st' : EStore) (r : LsIdx) :
    RelLs g st c st' r = MapRelG g (denoteLs st.lss c) (denoteLs st'.lss r) := by
  apply propext; constructor
  · intro h; cases hc : denoteLs st.lss c with
    | none => trivial
    | some u => exact h u hc
  · intro h u hu; rw [hu] at h; exact h

/-- con-leche: none — a `sort` view's level. -/
theorem DenoteView.sort {st : EStore} {u : LIdx} {e : Expr}
    (H : DenoteView st (some (.sort u)) (some e)) : denoteL st.ls u = some (exprSort e) := H
grind_pattern [bridge_grind] DenoteView.sort => DenoteView st (some (.sort u)) (some e)

/-- con-leche: none — an expression tagged `bvar` IS a bound variable. -/
theorem exprTag_bvar {e : Expr} (h : exprTag e = ETag.bvar) : e = .bvar (exprBVar e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_bvar => exprTag e where
  guard exprTag e = ETag.bvar

/-- con-leche: none — an expression tagged `sort` IS a sort. -/
theorem exprTag_sort {e : Expr} (h : exprTag e = ETag.sort) : e = .sort (exprSort e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_sort => exprTag e where
  guard exprTag e = ETag.sort

/-- con-leche: none — an expression tagged `const` IS a constant. -/
theorem exprTag_const {e : Expr} (h : exprTag e = ETag.const) :
    e = .const (exprConstName e) (exprConstLevels e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_const => exprTag e where
  guard exprTag e = ETag.const

/-- con-leche: none — an expression tagged `lit` IS a literal. -/
theorem exprTag_lit {e : Expr} (h : exprTag e = ETag.lit) : e = .lit (exprLit e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
grind_pattern [bridge_grind] exprTag_lit => exprTag e where
  guard exprTag e = ETag.lit

attribute [bridge_grind =] ENodeView.tagOf

/-- con-leche: none — a level handle that denotes has a view (the intern
specs' precondition on a `sort`'s level). -/
theorem lview_isSome {st : LStore} {c : LIdx} (hd : (denoteL st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  exact lview_isSome_of_denote hx
grind_pattern [bridge_grind] lview_isSome => (st.view c).isSome

/-- con-leche: none — a universe-argument list handle that denotes has a view
(the intern specs' precondition on a `const`'s levels). -/
theorem lsview_isSome {st : LsStore} {c : LsIdx} (hd : (denoteLs st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨w, hw, -⟩ := denoteLs_view hx
  rw [hw]; rfl
grind_pattern [bridge_grind] lsview_isSome => (st.view c).isSome

/-- con-leche: none — `MemoLOK.mono` with the table the same term. -/
theorem MemoLOK.le {f : Level → Level} {tbl : Std.HashMap LIdx LIdx} {st st' : EStore}
    (hm : MemoLOK f tbl st) (hx : st ≤ st') : MemoLOK f tbl st' := MemoLOK.mono hm hx rfl
grind_pattern [bridge_grind] MemoLOK.le => MemoLOK f tbl st, st ≤ st'

/-- con-leche: none — `MemoLsOK.mono` with the table the same term. -/
theorem MemoLsOK.le {f : List Level → List Level} {tbl : Std.HashMap LsIdx LsIdx}
    {st st' : EStore} (hm : MemoLsOK f tbl st) (hx : st ≤ st') : MemoLsOK f tbl st' :=
  MemoLsOK.mono hm hx rfl
grind_pattern [bridge_grind] MemoLsOK.le => MemoLsOK f tbl st, st ≤ st'

/-- con-leche: none — `ReadLCacheOK.mono` at the store order. -/
theorem ReadLCacheOK.le {tbl : Std.HashMap LIdx Level} {st st' : EStore}
    (h : ReadLCacheOK tbl st) (hx : st ≤ st') : ReadLCacheOK tbl st' := h.mono hx
grind_pattern [bridge_grind] ReadLCacheOK.le => ReadLCacheOK tbl st, st ≤ st'

/-- con-leche: none — `ReadLsCacheOK.mono` at the store order. -/
theorem ReadLsCacheOK.le {tbl : Std.HashMap LsIdx (List Level)} {st st' : EStore}
    (h : ReadLsCacheOK tbl st) (hx : st ≤ st') : ReadLsCacheOK tbl st' := h.mono hx
grind_pattern [bridge_grind] ReadLsCacheOK.le => ReadLsCacheOK tbl st, st ≤ st'

/-- con-leche: none — `ReadNCacheOK.mono` at the store order. -/
theorem ReadNCacheOK.le {tbl : Std.HashMap NIdx ConLeche.Name} {st st' : EStore}
    (h : ReadNCacheOK tbl st) (hx : st ≤ st') : ReadNCacheOK tbl st' := h.mono hx
grind_pattern [bridge_grind] ReadNCacheOK.le => ReadNCacheOK tbl st, st ≤ st'

/-- con-leche: none — arena infrastructure: `EStore.view` reads `pers`, `scr`
and `scratchOn` and nothing else. -/
def viewAt (p s : ETables) (on : Bool) (i : EIdx) : Option ENodeView :=
  if i.isPersistent then p.get i else if on then s.get i else none

/-- con-leche: none — `EStore.view` as a function of the three tables it
reads, so that congruence closure carries a view across a step that frames
them (`substLMemoAt` moves only the LEVEL store).  Passed to `sym` by the walk
that needs it. -/
theorem view_eq_viewAt (st : EStore) (i : EIdx) :
    st.view i = viewAt st.pers st.scr st.scratchOn i := by
  rw [EStore.view_eq_tier]; rfl

/-! ### Theorem 1 for `instLPGo` -/

-- The cache frame, `s'.caches = { s₁.caches with readLC := …, readLsC := … }`,
-- is structure eta at the cache record (`Bridge/Specs.lean`'s local line).
attribute [local bridge_grind ext] Caches

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `instLPGo`'s recursion.

**The frame is NOT `s'.caches = s₁.caches`** (`ExprOps/InstLP.lean`'s header
says why): the `sort` and `const` arms read a level back, and the memoised
readback WRITES `caches.readLC` / `caches.readLsC`.  What the walk preserves
instead — and what its own recursive calls need — is the two readback
CLAUSES, so those are hypotheses and conjuncts both. -/
structure InstLPSpec (ks : List ConLeche.Name) (us : List Level)
    (rec : EIdx → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx), StateOK s₁ → InstLPMemoF ks us s₁ →
    InstLPLMemoA ks us s₁ → InstLPLsMemoA ks us s₁ →
    ReadLCacheOK s₁.caches.readLC s₁.store →
    ReadLsCacheOK s₁.caches.readLsC s₁.store →
    (denoteE s₁.store h).isSome = true →
    ⦃fun s => s = s₁⦄ rec h
    ⦃fun r s' => StateOK s' ∧ InstLPMemoF ks us s' ∧ InstLPLMemoA ks us s' ∧
        InstLPLsMemoA ks us s' ∧ Ext s₁.store s'.store ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        s'.caches =
          { s₁.caches with
            readLC := s'.caches.readLC, readLsC := s'.caches.readLsC } ∧
        s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        InstLPAt ks us s₁.store h s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
**THEOREM 1 for `instantiateLevelParams`**, at one level of the recursion, by
induction on the fuel: the `hasLP` cutoff (`lpOfData_derived`,
`instLPFn_cutoff`), the view dispatch with its ten arms unfolded in place, the
two LEVEL arms by `ExprOps/InstLP.lean`'s specs. -/
theorem instLPGo_specS (ks : List ConLeche.Name) (us : List Level) :
    ∀ fuel, InstLPSpec ks us (instLPGo ks us fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _ _ _ _ _ _
    sym only [bridge_grind] => vcgen [instLPGo_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h hok hm hml hmls hcl hcls hden
    dsimp only
    sym only [bridge_grind, denoteEView, opt2, opt3, instLPFn_cutoff, view_eq_viewAt] =>
      vcgen [instLPGo_succ, instLPArmFVar, instLPArmApp, instLPArmLam,
        instLPArmForallE, instLPArmLet, instLPArmProj, ih.run,
        substLMemoAt_spec, substLsMemoAt_spec,
        instLPSet_specA (f := instLPFn ks us)] <;> finish (gen := 10)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the walk
at every substitution, as the entry's `vcgen` list takes it. -/
theorem instLPGo_spec (fuel : Nat) (ks : List ConLeche.Name) (us : List Level)
    (s₁ : AState) (h : EIdx) (hok : StateOK s₁) (hm : InstLPMemoF ks us s₁)
    (hml : InstLPLMemoA ks us s₁) (hmls : InstLPLsMemoA ks us s₁)
    (hcl : ReadLCacheOK s₁.caches.readLC s₁.store)
    (hcls : ReadLsCacheOK s₁.caches.readLsC s₁.store)
    (hden : (denoteE s₁.store h).isSome = true) :
    ⦃fun s => s = s₁⦄ instLPGo ks us fuel h
    ⦃fun r s' => StateOK s' ∧ InstLPMemoF ks us s' ∧ InstLPLMemoA ks us s' ∧
        InstLPLsMemoA ks us s' ∧ Ext s₁.store s'.store ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        s'.caches =
          { s₁.caches with
            readLC := s'.caches.readLC, readLsC := s'.caches.readLsC } ∧
        s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        InstLPAt ks us s₁.store h s'.store r; ⊤⦄ :=
  (instLPGo_specS ks us fuel).run s₁ h hok hm hml hmls hcl hcls hden

/-! ### The NAME readback with the sibling readback tables framed

`ExprOps/MemoSpecs.lean` did this for `readLevelM` / `readLevelsM`
(`readLevelM_specF`, `readLevelsM_specF`) and gives the reason: a walk that
reads more than one kind of handle back must carry the OTHER kind's cache
clause across.  `instLPFast` reads NAMES back and then LEVELS, so it needs
the third face of the same lemma, and `Bridge/SpecsL.lean`'s
`readNamesM_spec` does not frame `caches.readLC` / `caches.readLsC`.  These
two belong in `Bridge/SpecsL.lean` beside the specs they strengthen.

Round 4 made all four `_specF` faces carry the RECORD equation
`s'.caches = { s₀.caches with readNC := … }` instead of the two sibling-table
equations: the sibling equations are its projections, and the other eleven
cache tables come with it, which is what lets `instLPFast_spec` state a cache
frame at all. -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — `readNameM` with the
sibling readback tables framed. -/
@[spec high] theorem readNameM_specF (s₀ : AState) (h : NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => s = s₀⦄ readNameM h
    ⦃fun x s' => s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readNC := s'.caches.readNC } ∧
        denoteN s₀.store.ns h = some x ∧
        ReadNCacheOK s'.caches.readNC s'.store; ⊤⦄ := by
  dsimp only
  vcgen [readNameM]
  all_goals (subst_vars; refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadNCacheOK])

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — and `readNamesM`, whose
recursion is on the list as `readNames`' is. -/
@[spec high] theorem readNamesM_specF (s₀ : AState) (hs : List NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => s = s₀⦄ readNamesM hs
    ⦃fun xs s' => s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readNC := s'.caches.readNC } ∧
        Frontend.denoteNList s₀.store.ns hs = some xs ∧
        ReadNCacheOK s'.caches.readNC s'.store; ⊤⦄ := by
  dsimp only
  induction hs generalizing s₀ with
  | nil =>
    vcgen [readNamesM]
    all_goals (subst_vars; grind [Frontend.denoteNList, ReadNCacheOK])
  | cons a as ih =>
    -- `mvcgen` preferred `Bridge/SpecsL.lean`'s database `readNamesM_spec` to
    -- the induction hypothesis, so the tail used to be generalised to a
    -- program VARIABLE first; with `vcgen` the hypothesis passed in the list
    -- serves directly.
    sym only [bridge_grind, Frontend.denoteNList, ReadNCacheOK] =>
      vcgen [readNamesM, readNameM_specF, ih] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2718-2722 Expr.instLPFast — the
entry, which reads `ks` and `us` back ONCE (`readNamesM` / `readLevelsM`) and
then runs `instLPGo` on the transient trees.

**Two statement changes this round had to make** (the shape the round owed
was not provable):

* the frame is NOT `s'.caches = s₀.caches` — the readbacks and the walk's two
  level arms WRITE the readback caches (`ExprOps/InstLP.lean`'s header).  The
  two readback CLAUSES are carried instead, as hypotheses and conjuncts both;
  the THIRD (`ReadNCacheOK`, which `readNamesM` needs) is a hypothesis and
  cannot be a conjunct, because `ExprOps/InstLP.lean`'s `substLMemoAt_spec`
  does not frame `caches.readNC` — a one-conjunct change there would give it
  back;
* the memo clause is a DISJUNCTION, exactly as `abstractRangeFast_spec`'s is
  and for the same reason: the `hasLP` cutoff is HOISTED over the readbacks
  (task #97-P6-10), so on a level-parameter-free subject the entry returns
  without clearing anything. -/
theorem instLPFast_spec (fuel : Nat) (s₀ : AState) (ks : List NIdx)
    (us : LsIdx) (e : EIdx) (ksv : List ConLeche.Name) (usv : List Level)
    (hok : StateOK s₀)
    (hcn : ReadNCacheOK s₀.caches.readNC s₀.store)
    (hcl : ReadLCacheOK s₀.caches.readLC s₀.store)
    (hcls : ReadLsCacheOK s₀.caches.readLsC s₀.store)
    (hks : Frontend.denoteNList s₀.store.ns ks = some ksv)
    (hus : denoteLs s₀.store.lss us = some usv)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ instLPFast fuel ks us e
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        ReadLCacheOK s'.caches.readLC s'.store ∧
        ReadLsCacheOK s'.caches.readLsC s'.store ∧
        ReadNCacheOK s'.caches.readNC s'.store ∧
        s'.caches =
          { s₀.caches with
            readLC := s'.caches.readLC, readNC := s'.caches.readNC,
            readLsC := s'.caches.readLsC } ∧
        s'.pins = s₀.pins ∧
        (s'.memos.instLPC = ∅ ∨ s' = s₀) ∧
        RelE (fun x => x.instantiateLevelParams ksv usv) s₀.store e
          s'.store r; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind, instLPFn, Expr.instantiateLevelParams_eq_self, MemoOK.of_empty,
      MemoLOK.of_empty, MemoLsOK.of_empty] =>
    vcgen [instLPFast, instLPGo_spec fuel] <;> finish


/-! ## The axiom check -/

#print axioms abstract1Fast_spec
#print axioms abstractRangeGo_specS
#print axioms abstractRangeFast_spec
#print axioms instLPGo_specS
#print axioms instLPFast_spec

end ConRon.Bridge.ExprOps
