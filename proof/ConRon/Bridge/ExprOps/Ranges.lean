/-
# `ConRon.Bridge.ExprOps.Ranges` — Theorem 1 for the packed range fields

DESIGN §8.2's Theorem 1 at the eight twins of `Arena/ExprOps.lean` that read
or recompute the derived word's two 15-bit range fields: `bvarBoundGo`,
`bvarBoundMemo`, `fvarRangeGo`, `fvarRangeMemo`, `bvarB`, `fvarB`,
`hasFvarFast`, `looseBVarsBoundedFast`.  Companion of
`ExprOps/Walks.lean` (the unmemoized `Bool`/`Nat` walks) and
`ExprOps/Leaves.lean` (the leaf list and the leaf guard).

## What makes this group different from `Walks.lean`

**The saturation branch.**  `Expr.bvarB` is the packed field when it is
below `satRange` and the memoized recomputation otherwise, and the twin is
that `if` verbatim.  Three facts connect the three spellings:

* `EStore.derived_exact` (`Arena/WFProofs.lean`) — the store's derived column
  IS con-leche's `Expr.data` of the denoted term, so
  `bvarOfData (st.derived h)` is `Expr.bvarBRaw e`;
* `Expr.bvarBRaw_exact` (con-leche `ExprOps.lean:1456`) — below saturation
  the field is `Expr.bvarBound`;
* `Expr.bvarB_eq` (`:1577`) — and the accessor is `Expr.bvarBound`
  unconditionally, which is why every theorem below is stated against
  `Expr.bvarBound` / `Expr.fvarRange` and the `Expr.bvarB` / `Expr.fvarB`
  spelling is a one-line corollary (`bvarB_spec'`, `fvarB_spec'`).

`bvarBound_of_derived` and `fvarRange_of_derived` below package the first two
into the shape the `else` arm of the twin presents, and they are the two
`@[grind →]` rules the closer needs that `Bridge/Rel.lean` does not have.
**They morally belong in `Bridge/Rel.lean`.**

**The memo is in `AState`.**  Unlike `wscopedBGo`'s and `leavesSubGo`'s, the
`bvarBound` / `fvarRange` memo is one of `Bridge/StateOK.lean`'s thirteen
tables (`MemoBA` over `bvarBC`, `MemoFA` over `fvarBC`), so the invariant is
`MemoVOK` and `MemoVOK.get` / `.insert` / `.of_empty` carry it — exactly the
`Nat`-valued shape `StateOK.lean` says this group has.

## The frame

The store never moves here — nothing interns — so the postconditions say
`s'.store = s₁.store` rather than `Ext s₁.store s'.store`, and
`StateOK s'` is derivable from that equation rather than being a conjunct.
What does move is `s.memos.bvarBC` (resp. `fvarBC`), so `caches` and `pins`
are framed and the twelve other per-call tables are **not** — the same gap
`ExprOps/Inst1.lean` records, and the same reason (`internE_spec` and the
memo-set specs frame `memos` as a whole record update, which the `Go`
theorem's postcondition would have to thread).
-/
import ConRon.Bridge.Specs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ## The two derived-word licences

The one place this file unfolds the packed word.  Both are
`EStore.derived_exact` plus con-leche's own exactness theorem, stated as the
answer relation so that the arm proof never mentions either. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — **the
unsaturated branch's licence**: off saturation the store's derived word IS
`Expr.bvarBound` of the denoted term. -/
@[grind →] theorem bvarBound_of_derived {st : EStore} (hwf : StoreWF st)
    {h : EIdx} (hne : ¬ (bvarOfData (st.derived h)).toNat = satRange) :
    RelV Expr.bvarBound st h (bvarOfData (st.derived h)).toNat := by
  intro e he
  have hd := EStore.derived_exact hwf he
  rw [hd] at hne ⊢
  have hlt : Expr.bvarBRaw e < satRange := by
    have h1 := bvarOfData_lt e.data
    simp only [Expr.bvarBRaw, satRange] at hne ⊢
    omega
  exact Expr.bvarBRaw_exact e hlt

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1590 fvarBRaw_exact — the same at
the fvar-range field. -/
@[grind →] theorem fvarRange_of_derived {st : EStore} (hwf : StoreWF st)
    {h : EIdx} (hne : ¬ (fvarOfData (st.derived h)).toNat = satRange) :
    RelV Expr.fvarRange st h (fvarOfData (st.derived h)).toNat := by
  intro e he
  have hd := EStore.derived_exact hwf he
  rw [hd] at hne ⊢
  have hlt : Expr.fvarBRaw e < satRange := by
    have h1 := fvarOfData_lt e.data
    simp only [Expr.fvarBRaw, satRange] at hne ⊢
    omega
  exact Expr.fvarBRaw_exact e hlt

/-! ## The two readback equations the `Fast` twins need -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1308 looseBVarsBounded_iff — the
`iff` as the `Bool` equation `looseBVarsBoundedFast` computes. -/
theorem looseBVarsBounded_decide (e : Expr) (k : Nat) :
    decide (e.bvarBound ≤ k) = e.looseBVarsBounded k := by
  cases h : e.looseBVarsBounded k with
  | true => simp [Expr.looseBVarsBounded_iff.mp h]
  | false =>
    have hnb : ¬ (e.bvarBound ≤ k) := by
      intro hc
      rw [Expr.looseBVarsBounded_iff.mpr hc] at h
      exact absurd h (by simp)
    simp [hnb]

/-! ## `bvarBoundGo` — `ExprOps.lean:1408`

The memoized exact loose-bvar bound.  con-leche's `bvarBound` is the pure
specification and `bvarBoundGo` the memoized walk; the arena has one
function, and the memo is probed for every node, leaves included, as
con-leche probes it. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `bvarBoundGo`'s recursion. -/
structure BvarBoundSpec (rec : EIdx → AM Nat) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ → MemoBA s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c
    ⦃⇓? r s' => ⌜s'.store = s₁.store ∧ s'.caches = s₁.caches ∧
        s'.pins = s₁.pins ∧ MemoBA s' ∧
        RelV Expr.bvarBound s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1370-1394 bvarBoundGo — **THEOREM
1 for `bvarBound`**, at one level of the recursion, by induction on the
fuel. -/
theorem bvarBoundGo_spec : ∀ fuel, BvarBoundSpec (bvarBoundGo fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _ _
    mvcgen [bvarBoundGo]
    all_goals bridge_vcs [Expr.bvarBound, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hm hden
    have hrec := ih.run
    mvcgen [bvarBoundGo, hrec]
    all_goals bridge_vcs [Expr.bvarBound, RelV]

/-! ## `bvarBoundMemo` — `ExprOps.lean:1437`

The top-level entry: the memo is cleared before and after, so the call needs
no `MemoBA` hypothesis and leaves the table empty (`MemoVOK.of_empty` is what
makes a dropped table satisfy the invariant). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1396-1397 bvarBoundMemo —
**THEOREM 1 for `bvarBound`, at the entry point**. -/
theorem bvarBoundMemo_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarBoundMemo fuel e
    ⦃⇓? r s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos.bvarBC = ∅ ∧
        RelV Expr.bvarBound s₀.store e r⌝⦄ := by
  have hr := (bvarBoundGo_spec fuel).run
  mvcgen [bvarBoundMemo, hr]
  all_goals bridge_vcs [Expr.bvarBound, RelV]

/-! ## `fvarRangeGo` — `ExprOps.lean:1447`

`bvarBoundGo` at the other field: `fvar` annotations are NOT descended into
(matching the abstraction traversals), and the binder arms do not subtract
one. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `fvarRangeGo`'s recursion. -/
structure FvarRangeSpec (rec : EIdx → AM Nat) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ → MemoFA s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c
    ⦃⇓? r s' => ⌜s'.store = s₁.store ∧ s'.caches = s₁.caches ∧
        s'.pins = s₁.pins ∧ MemoFA s' ∧
        RelV Expr.fvarRange s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1399-1424 fvarRangeGo — **THEOREM
1 for `fvarRange`**, at one level of the recursion. -/
theorem fvarRangeGo_spec : ∀ fuel, FvarRangeSpec (fvarRangeGo fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _ _
    mvcgen [fvarRangeGo]
    all_goals bridge_vcs [Expr.fvarRange, RelV]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hm hden
    have hrec := ih.run
    mvcgen [fvarRangeGo, hrec]
    all_goals bridge_vcs [Expr.fvarRange, RelV]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1426-1427 fvarRangeMemo —
**THEOREM 1 for `fvarRange`, at the entry point**. -/
theorem fvarRangeMemo_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarRangeMemo fuel e
    ⦃⇓? r s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos.fvarBC = ∅ ∧
        RelV Expr.fvarRange s₀.store e r⌝⦄ := by
  have hr := (fvarRangeGo_spec fuel).run
  mvcgen [fvarRangeMemo, hr]
  all_goals bridge_vcs [Expr.fvarRange, RelV]

/-! ## `bvarB` and `fvarB` — `ExprOps.lean:1486`, `:1494`

**The `O(1)` derived-word reads with the saturation branch.**  Two arms: the
packed field below `satRange` (`bvarBound_of_derived` is the licence) and the
memoized recomputation at it.  The answer is `Expr.bvarBound` (resp.
`Expr.fvarRange`) in both, which is con-leche's `bvarB_eq` / `fvarB_eq`
proved one arm at a time. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1429-1434 bvarB — **THEOREM 1 for
`bvarB`**.  Stated at the exact function; `bvarB_spec'` below is the same
statement at con-leche's accessor. -/
theorem bvarB_spec (fuel : Nat) (s₀ : AState) (e : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ bvarB fuel e
    ⦃⇓? r s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ RelV Expr.bvarBound s₀.store e r⌝⦄ := by
  have hr := bvarBoundMemo_spec fuel
  mvcgen [bvarB, hr]
  all_goals bridge_vcs [RelV, bvarBound_of_derived]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1577 bvarB_eq — the same about a
RUN, and at con-leche's `Expr.bvarB`: the spelling the checker's cutoffs
read.  `RelV.congr` at `bvarB_eq` is the whole step. -/
theorem bvarB_run {fuel : Nat} {s₀ s' : AState} {e : EIdx} {r : Nat}
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (bvarB fuel e).run s₀ = Except.ok (r, s')) :
    s'.store = s₀.store ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
      RelV Expr.bvarBound s₀.store e r ∧ RelV Expr.bvarB s₀.store e r := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    AM.of_run (P := fun s => s = s₀) rfl hrun (bvarB_spec fuel s₀ e hok hden)
  exact ⟨h1, h2, h3, h4, h4.congr (fun x => (Expr.bvarB_eq x).symm)⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1436-1441 fvarB — **THEOREM 1 for
`fvarB`**. -/
theorem fvarB_spec (fuel : Nat) (s₀ : AState) (e : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarB fuel e
    ⦃⇓? r s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ RelV Expr.fvarRange s₀.store e r⌝⦄ := by
  have hr := fvarRangeMemo_spec fuel
  mvcgen [fvarB, hr]
  all_goals bridge_vcs [RelV, fvarRange_of_derived]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1698 fvarB_eq — the run form, at
`Expr.fvarRange` and at con-leche's `Expr.fvarB`. -/
theorem fvarB_run {fuel : Nat} {s₀ s' : AState} {e : EIdx} {r : Nat}
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (fvarB fuel e).run s₀ = Except.ok (r, s')) :
    s'.store = s₀.store ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
      RelV Expr.fvarRange s₀.store e r ∧ RelV Expr.fvarB s₀.store e r := by
  obtain ⟨h1, h2, h3, h4⟩ :=
    AM.of_run (P := fun s => s = s₀) rfl hrun (fvarB_spec fuel s₀ e hok hden)
  exact ⟨h1, h2, h3, h4, h4.congr (fun x => (Expr.fvarB_eq x).symm)⟩

/-! ## `hasFvarFast` and `looseBVarsBoundedFast` — `ExprOps.lean:1501`, `:1507`

The two `@[csimp]` replacements: what con-leche executes for `hasFvar` and
`looseBVarsBounded`, and what the arena executes too.  Each is the field read
plus one `Bool` equation — `Expr.fvarRange_bne_zero` and
`looseBVarsBounded_decide` above. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1709-1710 hasFvarFast — **THEOREM
1 for `hasFvarFast`**, at `hasFvar` (which is what `@[csimp]` says it
computes). -/
theorem hasFvarFast_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ hasFvarFast fuel e
    ⦃⇓? r s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ RelV Expr.hasFvar s₀.store e r⌝⦄ := by
  have hr := fvarB_spec fuel
  mvcgen [hasFvarFast, hr]
  all_goals bridge_vcs [RelV, Expr.fvarRange_bne_zero]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1718-1719 looseBVarsBoundedFast —
**THEOREM 1 for `looseBVarsBoundedFast`**, at `looseBVarsBounded`. -/
theorem looseBVarsBoundedFast_spec (fuel k : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ looseBVarsBoundedFast fuel k e
    ⦃⇓? r s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        RelV (Expr.looseBVarsBounded k) s₀.store e r⌝⦄ := by
  have hr := bvarB_spec fuel
  mvcgen [looseBVarsBoundedFast, hr]
  all_goals bridge_vcs [RelV, looseBVarsBounded_decide]

/-! ## The axiom check -/

#print axioms bvarBound_of_derived
#print axioms fvarRange_of_derived
#print axioms bvarBoundGo_spec
#print axioms bvarBoundMemo_spec
#print axioms fvarRangeGo_spec
#print axioms fvarRangeMemo_spec
#print axioms bvarB_spec
#print axioms fvarB_spec
#print axioms hasFvarFast_spec
#print axioms looseBVarsBoundedFast_spec

end ConRon.Bridge.ExprOps
