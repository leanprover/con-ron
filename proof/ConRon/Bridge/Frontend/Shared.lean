/-
# `ConRon.Bridge.Frontend.Shared` — the memoised readback IS the denotation,
and its inverse

`Arena/Frontend/Readback.lean`'s module note states the obligation this module
discharges, in its own words:

> `denoteEShared st h = denoteE st h` is the exactness obligation this owes
> P3; the two differ only in how many times the tree is built.

The reason the two functions exist at all is measured, not stylistic:
`Arena/Denote.lean`'s `denoteE` recurses at each child independently, so on a
DAG whose expression table doubles at every second entry (con-leche's own
`tests/e2e/tower_struct.ndjson`) it unfolds the sharing and does not finish.
`denoteEGo` threads a `Std.HashMap EIdx Expr` and rebuilds each node once.
**The value is the same and the sharing is the same; only the work differs.**

## What the equation costs

The memo makes the induction a two-parameter one — the fuel AND the memo's
own invariant — and the invariant is exactly the shape task #97-P3-0 §6
records for `fvarLeavesGo_spec`:

    DMemoOK st m  :  ∀ h e, m[h]? = some e → denoteE st h = some e

with the difference that `denoteEGo`'s memo is WHITE (a node is inserted after
its children are built), so there is no gray phase and no second induction on
`StoreWF`'s rank.  That is why this one is a straight fuel induction where
`fvarLeavesGo_spec`'s is not.

## The other direction

`internExpr` is the readback's inverse and the frontend needs it in three
places — the modeller seam (`Arena/Frontend/InModel.lean`), the pin variants
(`Bridge/Checker/Pins.lean`'s item 13) and `ProjRec`'s two recognisers until
P2d twinned them.  Its exactness is the mirror statement, `denoteE st'
(internExpr e) = some e`, with `Ext` and `StoreWF` threaded: it is
`Bridge/Specs.lean`'s `internE_spec` composed along a `ConLeche.Expr`'s own
structural recursion, with the `EMemo` invariant in the same shape.
-/
import ConRon.Bridge.Frontend.Rel
import ConRon.Arena.Frontend.Readback

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The readback's memo -/

/-- con-leche: none — the readback memo's invariant: every recorded value is
the handle's own denotation.  `Bridge/StateOK.lean`'s `MemoOK` shape at
`denoteE` instead of at a pure walk. -/
def DMemoOK (st : EStore) (m : DMemo) : Prop :=
  ∀ h e, m[h]? = some e → denoteE st h = some e

theorem DMemoOK.empty (st : EStore) : DMemoOK st (∅ : DMemo) := by
  intro h e hm; simp at hm

/-- con-leche: none — the memo's one write: `denoteEGo` inserts a node AFTER
its children are built, so the row it writes is a true denotation.  This is
the WHITE half of `Bridge/StateOK.lean`'s `MemoOK.insert`; the gray one
(`Bridge/ExprOps/Leaves.lean`'s `seen` set) has no counterpart here. -/
theorem DMemoOK.insert {st : EStore} {m : DMemo} (hm : DMemoOK st m) {h : EIdx}
    {e : Expr} (hd : denoteE st h = some e) : DMemoOK st (m.insert h e) := by
  intro k x hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i heq
    obtain rfl : h = k := by simpa using heq
    simp only [Option.some.injEq] at hk
    subst hk; exact hd
  · exact hm k x hk

/-- con-leche: none — **the memoised readback's step**: at a memo that records
only true denotations, `denoteEGo` answers `denoteE` and leaves the memo
recording only true denotations.

The ten-arm fuel induction.  Every arm has the same three moves: the node's
view is `denoteE`'s own unfolding (`Arena/WFProofs.lean`'s `denoteE_unfold`,
which is where `StoreWF` is spent), the children are the induction
hypothesis's, and the row the arm writes is a true denotation because it is
written AFTER them (`DMemoOK.insert`).  The memo is WHITE, so unlike
`Bridge/ExprOps/Leaves.lean`'s `fvarLeavesGo_spec` there is no gray phase and
no second induction on `StoreWF`'s rank. -/
theorem denoteEGo_spec_le {st : EStore} (hwf : StoreWF st) :
    ∀ (fuel : Nat) {m m' : DMemo}, DMemoOK st m → ∀ {h : EIdx} {e : Expr},
      denoteEGo st m fuel h = some (m', e) →
        denoteE st h = some e ∧ DMemoOK st m' := by
  obtain ⟨rk, hwf'⟩ := hwf
  intro fuel
  induction fuel with
  | zero => intro m m' hm h e hrun; simp [denoteEGo] at hrun
  | succ f ih =>
    intro m m' hm h e hrun
    rw [denoteEGo] at hrun
    cases hmem : m[h]? with
    | some x =>
      rw [hmem] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨h1, h2⟩ := hrun
      subst h1; subst h2
      exact ⟨hm h x hmem, hm⟩
    | none =>
    rw [hmem] at hrun
    cases hv : st.view h with
    | none => rw [hv] at hrun; simp at hrun
    | some v =>
    rw [hv] at hrun
    have hun : denoteE st h = denoteEView st v := denoteE_unfold hwf' hv
    cases v with
    | bvar k =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hme, hee⟩ := hrun
      subst hee; subst hme
      have hde : denoteE st h = some (Expr.bvar k) := by rw [hun]; rfl
      exact ⟨hde, hm.insert hde⟩
    | lit l =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hme, hee⟩ := hrun
      subst hee; subst hme
      have hde : denoteE st h = some (Expr.lit l) := by rw [hun]; rfl
      exact ⟨hde, hm.insert hde⟩
    | sort u =>
      simp only [] at hrun
      cases hl : denoteL st.ls u with
      | none => rw [hl] at hrun; simp at hrun
      | some l =>
        rw [hl] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hee⟩ := hrun
        subst hee; subst hme
        have hde : denoteE st h = some (Expr.sort l) := by
          rw [hun]; simp [denoteEView, hl]
        exact ⟨hde, hm.insert hde⟩
    | const n us =>
      simp only [] at hrun
      cases hn : denoteN st.ns n with
      | none => rw [hn] at hrun; simp at hrun
      | some nm =>
        cases hls : denoteLs st.lss us with
        | none => rw [hn, hls] at hrun; simp at hrun
        | some ls =>
          rw [hn, hls] at hrun
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨hme, hee⟩ := hrun
          subst hee; subst hme
          have hde : denoteE st h = some (Expr.const nm ls) := by
            rw [hun]; simp [denoteEView, opt2, hn, hls]
          exact ⟨hde, hm.insert hde⟩
    | fvar k ty =>
      simp only [] at hrun
      cases h1 : denoteEGo st m f ty with
      | none => rw [h1] at hrun; simp at hrun
      | some p1 =>
        obtain ⟨m1, t⟩ := p1
        rw [h1] at hrun
        obtain ⟨hdt, hm1⟩ := ih hm h1
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hee⟩ := hrun
        subst hee; subst hme
        have hde : denoteE st h = some (Expr.fvar k t) := by
          rw [hun]; simp [denoteEView, hdt]
        exact ⟨hde, hm1.insert hde⟩
    | app g a =>
      simp only [] at hrun
      cases h1 : denoteEGo st m f g with
      | none => rw [h1] at hrun; simp at hrun
      | some p1 =>
        obtain ⟨m1, ef⟩ := p1
        rw [h1] at hrun
        simp only [] at hrun
        obtain ⟨hdf, hm1⟩ := ih hm h1
        cases h2 : denoteEGo st m1 f a with
        | none => rw [h2] at hrun; simp at hrun
        | some p2 =>
          obtain ⟨m2, ea⟩ := p2
          rw [h2] at hrun
          obtain ⟨hda, hm2⟩ := ih hm1 h2
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨hme, hee⟩ := hrun
          subst hee; subst hme
          have hde : denoteE st h = some (Expr.app ef ea) := by
            rw [hun]; simp [denoteEView, opt2, hdf, hda]
          exact ⟨hde, hm2.insert hde⟩
    | lam ty b bi =>
      simp only [] at hrun
      cases h1 : denoteEGo st m f ty with
      | none => rw [h1] at hrun; simp at hrun
      | some p1 =>
        obtain ⟨m1, et⟩ := p1
        rw [h1] at hrun
        simp only [] at hrun
        obtain ⟨hdt, hm1⟩ := ih hm h1
        cases h2 : denoteEGo st m1 f b with
        | none => rw [h2] at hrun; simp at hrun
        | some p2 =>
          obtain ⟨m2, eb⟩ := p2
          rw [h2] at hrun
          obtain ⟨hdb, hm2⟩ := ih hm1 h2
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨hme, hee⟩ := hrun
          subst hee; subst hme
          have hde : denoteE st h = some (Expr.lam et eb bi) := by
            rw [hun]; simp [denoteEView, opt2, hdt, hdb]
          exact ⟨hde, hm2.insert hde⟩
    | forallE ty b bi =>
      simp only [] at hrun
      cases h1 : denoteEGo st m f ty with
      | none => rw [h1] at hrun; simp at hrun
      | some p1 =>
        obtain ⟨m1, et⟩ := p1
        rw [h1] at hrun
        simp only [] at hrun
        obtain ⟨hdt, hm1⟩ := ih hm h1
        cases h2 : denoteEGo st m1 f b with
        | none => rw [h2] at hrun; simp at hrun
        | some p2 =>
          obtain ⟨m2, eb⟩ := p2
          rw [h2] at hrun
          obtain ⟨hdb, hm2⟩ := ih hm1 h2
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨hme, hee⟩ := hrun
          subst hee; subst hme
          have hde : denoteE st h = some (Expr.forallE et eb bi) := by
            rw [hun]; simp [denoteEView, opt2, hdt, hdb]
          exact ⟨hde, hm2.insert hde⟩
    | letE ty w b =>
      simp only [] at hrun
      cases h1 : denoteEGo st m f ty with
      | none => rw [h1] at hrun; simp at hrun
      | some p1 =>
        obtain ⟨m1, et⟩ := p1
        rw [h1] at hrun
        simp only [] at hrun
        obtain ⟨hdt, hm1⟩ := ih hm h1
        cases h2 : denoteEGo st m1 f w with
        | none => rw [h2] at hrun; simp at hrun
        | some p2 =>
          obtain ⟨m2, ev⟩ := p2
          rw [h2] at hrun
          simp only [] at hrun
          obtain ⟨hdv, hm2⟩ := ih hm1 h2
          cases h3 : denoteEGo st m2 f b with
          | none => rw [h3] at hrun; simp at hrun
          | some p3 =>
            obtain ⟨m3, eb⟩ := p3
            rw [h3] at hrun
            obtain ⟨hdb, hm3⟩ := ih hm2 h3
            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨hme, hee⟩ := hrun
            subst hee; subst hme
            have hde : denoteE st h = some (Expr.letE et ev eb) := by
              rw [hun]; simp [denoteEView, opt3, hdt, hdv, hdb]
            exact ⟨hde, hm3.insert hde⟩
    | proj n i sub =>
      simp only [] at hrun
      cases hn : denoteN st.ns n with
      | none => rw [hn] at hrun; simp at hrun
      | some nm =>
        cases h1 : denoteEGo st m f sub with
        | none => rw [hn, h1] at hrun; simp at hrun
        | some p1 =>
          obtain ⟨m1, es⟩ := p1
          rw [hn, h1] at hrun
          simp only [] at hrun
          obtain ⟨hds, hm1⟩ := ih hm h1
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨hme, hee⟩ := hrun
          subst hee; subst hme
          have hde : denoteE st h = some (Expr.proj nm i es) := by
            rw [hun]; simp [denoteEView, opt2, hn, hds]
          exact ⟨hde, hm1.insert hde⟩

/-- con-leche: none — **the memoised readback's step**, as the tier states
it. -/
theorem denoteEGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {fuel : Nat} {h : EIdx} {e : Expr}
    (hrun : denoteEGo st m fuel h = some (m', e)) :
    denoteE st h = some e ∧ DMemoOK st m' :=
  denoteEGo_spec_le hwf fuel hm hrun

/-- con-leche: none — **`denoteEShared` IS `denoteE`**
(`Arena/Frontend/Readback.lean`'s own stated obligation, in the direction it
is used: whatever the memoised readback answers, the plain denotation
answers).

The converse — `denoteE` answering means `denoteEShared` answers — needs the
fuel to be enough, which is `StoreWF`'s rank bound; it is `denoteEShared_isSome`
below and it is the half `ctxOf` needs. -/
theorem denoteEShared_eq {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (hrun : denoteEShared st h = some e) : denoteE st h = some e := by
  simp only [denoteEShared] at hrun
  cases hgo : denoteEGo st (∅ : DMemo) (st.nodeCount + 1) h with
  | none => rw [hgo] at hrun; exact absurd hrun (by simp)
  | some p =>
    rw [hgo] at hrun
    simp only [Option.some.injEq] at hrun
    subst hrun
    exact (denoteEGo_spec hwf (DMemoOK.empty st) hgo).1

/-- con-leche: none — the other half of the same equation: a handle that
denotes reads back.  The store's node count bounds every path through it (a
child is interned before its parent), which is `storeFuel`'s own justification
in `Arena/Frontend/ExportC.lean`.

`sorry`: the rank induction of `Arena/WFProofs.lean`, run at `denoteEGo`
instead of at `denoteE`.  Task #97-P3-Frontend's sorry list, item 1. -/
theorem denoteEShared_isSome {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} (hd : denoteE st h = some e) : denoteEShared st h = some e := by
  sorry

/-- con-leche: none — the equation in full, as
`Arena/Frontend/Readback.lean`'s note writes it. -/
theorem denoteEShared_eq_denoteE {st : EStore} (hwf : StoreWF st) (h : EIdx) :
    denoteEShared st h = denoteE st h := by
  cases hd : denoteE st h with
  | none =>
    cases hs : denoteEShared st h with
    | none => rfl
    | some e => rw [denoteEShared_eq hwf hs] at hd; exact absurd hd (by simp)
  | some e => exact denoteEShared_isSome hwf hd

/-! ## The declaration layer's memoised readback

`denoteCVGo` / `denoteCIGo` / `denoteCIListGo` are `denoteEGo` threaded
through the records, and `readExpr` / `readCIList` are their `AM` faces.  Each
is the same equation at one more layer. -/

/-- con-leche: none — the memoised readback at an expression LIST. -/
theorem denoteEListGo_spec {st : EStore} (hwf : StoreWF st) :
    ∀ (hs : List EIdx) {m m' : DMemo} {es : List Expr}, DMemoOK st m →
      denoteEListGo st m hs = some (m', es) →
        denoteEList st hs = some es ∧ DMemoOK st m' := by
  intro hs
  induction hs with
  | nil =>
    intro m m' es hm hrun
    simp only [denoteEListGo, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun
    subst h1; subst h2
    exact ⟨rfl, hm⟩
  | cons h hs ih =>
    intro m m' es hm hrun
    rw [denoteEListGo] at hrun
    cases h1 : denoteEGo st m (st.nodeCount + 1) h with
    | none => rw [h1] at hrun; simp at hrun
    | some p1 =>
      obtain ⟨m1, e⟩ := p1
      rw [h1] at hrun
      simp only [] at hrun
      obtain ⟨hde, hm1⟩ := denoteEGo_spec hwf hm h1
      cases h2 : denoteEListGo st m1 hs with
      | none => rw [h2] at hrun; simp at hrun
      | some p2 =>
        obtain ⟨m2, xs⟩ := p2
        rw [h2] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hee⟩ := hrun
        obtain ⟨hdl, hm2⟩ := ih hm1 h2
        subst hee; subst hme
        exact ⟨by simp only [denoteEList, hde, hdl], hm2⟩

/-- con-leche: none — the memoised `ConstantVal` readback is
`Bridge/Rel.lean`'s `denoteCV`: three reads and `denoteEGo_spec`. -/
theorem denoteCVGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {cv : IConstantVal} {c : ConstantVal}
    (hrun : denoteCVGo st m cv = some (m', c)) :
    denoteCV st cv = some c ∧ DMemoOK st m' := by
  rw [denoteCVGo] at hrun
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at hrun; simp at hrun
  | some n =>
  cases hlp : denoteNList st.ns cv.levelParams with
  | none => rw [hn, hlp] at hrun; simp at hrun
  | some lps =>
  cases ht : denoteEGo st m (st.nodeCount + 1) cv.type with
  | none => rw [hn, hlp, ht] at hrun; simp at hrun
  | some p =>
  obtain ⟨m1, ty⟩ := p
  rw [hn, hlp, ht] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hme, hce⟩ := hrun
  obtain ⟨hdt, hm1⟩ := denoteEGo_spec hwf hm ht
  subst hce; subst hme
  exact ⟨by simp only [denoteCV, hn, hlp, hdt], hm1⟩

/-- con-leche: none — the memoised readback of a rule's firing mode. -/
theorem denoteFireGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {fr : IRecRuleFire} {f : RecRuleFire}
    (hrun : denoteFireGo st m fr = some (m', f)) :
    denoteFire st fr = some f ∧ DMemoOK st m' := by
  cases fr with
  | inert =>
    simp only [denoteFireGo, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun; subst h1; subst h2; exact ⟨rfl, hm⟩
  | plain =>
    simp only [denoteFireGo, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun; subst h1; subst h2; exact ⟨rfl, hm⟩
  | nested lvls pins =>
    rw [denoteFireGo] at hrun
    cases hl : denoteLList st.ls lvls with
    | none => rw [hl] at hrun; simp at hrun
    | some ls =>
    cases hp : denoteEListGo st m pins with
    | none => rw [hl, hp] at hrun; simp at hrun
    | some q =>
    obtain ⟨m1, ps⟩ := q
    rw [hl, hp] at hrun
    simp only [Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨hme, hfe⟩ := hrun
    obtain ⟨hdp, hm1⟩ := denoteEListGo_spec hwf pins hm hp
    subst hfe; subst hme
    exact ⟨by simp only [denoteFire, hl, hdp], hm1⟩

/-- con-leche: none — the memoised readback of one recursor rule. -/
theorem denoteRuleGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {rl : IRecRule} {r : RecRule}
    (hrun : denoteRuleGo st m rl = some (m', r)) :
    denoteRule st rl = some r ∧ DMemoOK st m' := by
  rw [denoteRuleGo] at hrun
  cases hc : denoteN st.ns rl.ctor with
  | none => rw [hc] at hrun; simp at hrun
  | some c =>
  cases hf : denoteFireGo st m rl.fire with
  | none => rw [hc, hf] at hrun; simp at hrun
  | some p =>
  obtain ⟨m1, f⟩ := p
  rw [hc, hf] at hrun
  simp only [] at hrun
  obtain ⟨hdf, hm1⟩ := denoteFireGo_spec hwf hm hf
  cases hr : denoteEGo st m1 (st.nodeCount + 1) rl.rhs with
  | none => rw [hr] at hrun; simp at hrun
  | some q =>
  obtain ⟨m2, rhs⟩ := q
  rw [hr] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hme, hre⟩ := hrun
  obtain ⟨hdr, hm2⟩ := denoteEGo_spec hwf hm1 hr
  subst hre; subst hme
  exact ⟨by simp only [denoteRule, hc, hdf, hdr], hm2⟩

/-- con-leche: none — the memoised readback of a rule list. -/
theorem denoteRulesGo_spec {st : EStore} (hwf : StoreWF st) :
    ∀ (rs : List IRecRule) {m m' : DMemo} {xs : List RecRule}, DMemoOK st m →
      denoteRulesGo st m rs = some (m', xs) →
        denoteRules st rs = some xs ∧ DMemoOK st m' := by
  intro rs
  induction rs with
  | nil =>
    intro m m' xs hm hrun
    simp only [denoteRulesGo, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun; subst h1; subst h2; exact ⟨rfl, hm⟩
  | cons r rs ih =>
    intro m m' xs hm hrun
    rw [denoteRulesGo] at hrun
    cases h1 : denoteRuleGo st m r with
    | none => rw [h1] at hrun; simp at hrun
    | some p1 =>
      obtain ⟨m1, x⟩ := p1
      rw [h1] at hrun
      simp only [] at hrun
      obtain ⟨hdr, hm1⟩ := denoteRuleGo_spec hwf hm h1
      cases h2 : denoteRulesGo st m1 rs with
      | none => rw [h2] at hrun; simp at hrun
      | some p2 =>
        obtain ⟨m2, ys⟩ := p2
        rw [h2] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hxe⟩ := hrun
        obtain ⟨hdl, hm2⟩ := ih hm1 h2
        subst hxe; subst hme
        exact ⟨by simp only [denoteRules, hdr, hdl], hm2⟩

/-- con-leche: none — the memoised readback of a projection table. -/
theorem denoteProjTableGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {t : IProjTable} {tbl : ProjTable}
    (hrun : denoteProjTableGo st m t = some (m', tbl)) :
    denoteProjTable st t = some tbl ∧ DMemoOK st m' := by
  rw [denoteProjTableGo] at hrun
  cases hsn : denoteN st.ns t.structName with
  | none => rw [hsn] at hrun; simp at hrun
  | some sn =>
  cases hlp : denoteNList st.ns t.levelParams with
  | none => rw [hsn, hlp] at hrun; simp at hrun
  | some lps =>
  cases hct : denoteN st.ns t.ctor with
  | none => rw [hsn, hlp, hct] at hrun; simp at hrun
  | some ct =>
  rw [hsn, hlp, hct] at hrun
  simp only [] at hrun
  cases hss : denoteL st.ls t.structSort with
  | none => rw [hss] at hrun; simp at hrun
  | some ss =>
  cases hb : denoteEListGo st m t.bodies.toList with
  | none => rw [hss, hb] at hrun; simp at hrun
  | some q =>
  obtain ⟨m1, bs⟩ := q
  cases hg : denoteLList st.ls t.guards with
  | none => rw [hss, hb, hg] at hrun; simp at hrun
  | some gs =>
  rw [hss, hb, hg] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hme, hte⟩ := hrun
  obtain ⟨hdb, hm1⟩ := denoteEListGo_spec hwf _ hm hb
  subst hte; subst hme
  exact ⟨by simp only [denoteProjTable, hsn, hlp, hct, hss, hg, denoteEArray, hdb],
    hm1⟩

/-- con-leche: none — the memoised readback of one stored constant. -/
theorem denoteCIGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {c : IConstantInfo} {cP : ConstantInfo}
    (hrun : denoteCIGo st m c = some (m', cP)) :
    denoteCI st c = some cP ∧ DMemoOK st m' := by
  cases c with
  | axiomInfo v =>
    rw [denoteCIGo] at hrun
    cases h1 : denoteCVGo st m v with
    | none => rw [h1] at hrun; simp at hrun
    | some p =>
      obtain ⟨m1, cv⟩ := p
      rw [h1] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hme, hce⟩ := hrun
      obtain ⟨hdv, hm1⟩ := denoteCVGo_spec hwf hm h1
      subst hce; subst hme
      exact ⟨by simp [denoteCI, hdv], hm1⟩
  | ctorInfo v nP nF =>
    rw [denoteCIGo] at hrun
    cases h1 : denoteCVGo st m v with
    | none => rw [h1] at hrun; simp at hrun
    | some p =>
      obtain ⟨m1, cv⟩ := p
      rw [h1] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hme, hce⟩ := hrun
      obtain ⟨hdv, hm1⟩ := denoteCVGo_spec hwf hm h1
      subst hce; subst hme
      exact ⟨by simp [denoteCI, hdv], hm1⟩
  | defnInfo v e hint =>
    rw [denoteCIGo] at hrun
    cases h1 : denoteCVGo st m v with
    | none => rw [h1] at hrun; simp at hrun
    | some p =>
      obtain ⟨m1, cv⟩ := p
      rw [h1] at hrun
      simp only [] at hrun
      obtain ⟨hdv, hm1⟩ := denoteCVGo_spec hwf hm h1
      cases h2 : denoteEGo st m1 (st.nodeCount + 1) e with
      | none => rw [h2] at hrun; simp at hrun
      | some q =>
        obtain ⟨m2, x⟩ := q
        rw [h2] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hce⟩ := hrun
        obtain ⟨hdx, hm2⟩ := denoteEGo_spec hwf hm1 h2
        subst hce; subst hme
        exact ⟨by simp [denoteCI, hdv, hdx], hm2⟩
  | thmInfo v e =>
    rw [denoteCIGo] at hrun
    cases h1 : denoteCVGo st m v with
    | none => rw [h1] at hrun; simp at hrun
    | some p =>
      obtain ⟨m1, cv⟩ := p
      rw [h1] at hrun
      simp only [] at hrun
      obtain ⟨hdv, hm1⟩ := denoteCVGo_spec hwf hm h1
      cases h2 : denoteEGo st m1 (st.nodeCount + 1) e with
      | none => rw [h2] at hrun; simp at hrun
      | some q =>
        obtain ⟨m2, x⟩ := q
        rw [h2] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hce⟩ := hrun
        obtain ⟨hdx, hm2⟩ := denoteEGo_spec hwf hm1 h2
        subst hce; subst hme
        exact ⟨by simp [denoteCI, hdv, hdx], hm2⟩
  | indInfo v caps =>
    rw [denoteCIGo] at hrun
    cases h1 : denoteCVGo st m v with
    | none => rw [h1] at hrun; simp at hrun
    | some p =>
      obtain ⟨m1, cv⟩ := p
      cases h2 : denoteCaps st caps with
      | none => rw [h1, h2] at hrun; simp at hrun
      | some cps =>
        rw [h1, h2] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hce⟩ := hrun
        obtain ⟨hdv, hm1⟩ := denoteCVGo_spec hwf hm h1
        subst hce; subst hme
        exact ⟨by simp [denoteCI, hdv, h2], hm1⟩
  | recInfo v mI rP rs =>
    rw [denoteCIGo] at hrun
    cases h1 : denoteCVGo st m v with
    | none => rw [h1] at hrun; simp at hrun
    | some p =>
      obtain ⟨m1, cv⟩ := p
      rw [h1] at hrun
      simp only [] at hrun
      obtain ⟨hdv, hm1⟩ := denoteCVGo_spec hwf hm h1
      cases h2 : denoteRulesGo st m1 rs with
      | none => rw [h2] at hrun; simp at hrun
      | some q =>
        obtain ⟨m2, rules⟩ := q
        rw [h2] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hce⟩ := hrun
        obtain ⟨hdr, hm2⟩ := denoteRulesGo_spec hwf rs hm1 h2
        subst hce; subst hme
        exact ⟨by simp [denoteCI, hdv, hdr], hm2⟩
  | projInfo t =>
    rw [denoteCIGo] at hrun
    cases h1 : denoteProjTableGo st m t with
    | none => rw [h1] at hrun; simp at hrun
    | some p =>
      obtain ⟨m1, tbl⟩ := p
      rw [h1] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨hme, hce⟩ := hrun
      obtain ⟨hdt, hm1⟩ := denoteProjTableGo_spec hwf hm h1
      subst hce; subst hme
      exact ⟨by simp [denoteCI, hdt], hm1⟩

/-- con-leche: none — the memoised block readback is `Bridge/Rel.lean`'s
`denoteCIList`.  This is the one `readCIList` (hence the modeller seam)
runs. -/
theorem denoteCIListGo_spec {st : EStore} (hwf : StoreWF st) :
    ∀ (cs : List IConstantInfo) {m m' : DMemo} {csP : List ConstantInfo},
      DMemoOK st m → denoteCIListGo st m cs = some (m', csP) →
        denoteCIList st cs = some csP ∧ DMemoOK st m' := by
  intro cs
  induction cs with
  | nil =>
    intro m m' csP hm hrun
    simp only [denoteCIListGo, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun; subst h1; subst h2; exact ⟨rfl, hm⟩
  | cons c cs ih =>
    intro m m' csP hm hrun
    rw [denoteCIListGo] at hrun
    cases h1 : denoteCIGo st m c with
    | none => rw [h1] at hrun; simp at hrun
    | some p1 =>
      obtain ⟨m1, x⟩ := p1
      rw [h1] at hrun
      simp only [] at hrun
      obtain ⟨hdc, hm1⟩ := denoteCIGo_spec hwf hm h1
      cases h2 : denoteCIListGo st m1 cs with
      | none => rw [h2] at hrun; simp at hrun
      | some p2 =>
        obtain ⟨m2, ys⟩ := p2
        rw [h2] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨hme, hxe⟩ := hrun
        obtain ⟨hdl, hm2⟩ := ih hm1 h2
        subst hxe; subst hme
        exact ⟨by simp only [denoteCIList, hdc, hdl], hm2⟩

/-- con-leche: none — `readExpr`, the `AM` face: it never moves the store and
its answer is the denotation. -/
theorem readExpr_run {s s' : AState} (hok : StateOK s) {h : EIdx} {e : Expr}
    (hrun : readExpr h s = .ok (e, s')) :
    s' = s ∧ denoteE s.store h = some e := by
  rw [readExpr] at hrun
  obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
  obtain ⟨ht, hs₁⟩ := AM.get_ok hget
  rw [ht, hs₁] at hrest
  cases hd : denoteEShared s.store h with
  | none => rw [hd] at hrest; exact absurd (AM.fail_ok hrest) (by simp)
  | some x =>
    rw [hd] at hrest
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest
    subst hv; subst hs
    exact ⟨rfl, denoteEShared_eq hok.wf hd⟩

/-- con-leche: none — `readCIList`, the `AM` face. -/
theorem readCIList_run {s s' : AState} (hok : StateOK s)
    {cs : List IConstantInfo} {csP : List ConstantInfo}
    (hrun : readCIList cs s = .ok (csP, s')) :
    s' = s ∧ denoteCIList s.store cs = some csP := by
  rw [readCIList] at hrun
  obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
  obtain ⟨ht, hs₁⟩ := AM.get_ok hget
  rw [ht, hs₁] at hrest
  cases hd : denoteCIListGo s.store ∅ cs with
  | none => rw [hd] at hrest; exact absurd (AM.fail_ok hrest) (by simp)
  | some p =>
    obtain ⟨m1, xs⟩ := p
    rw [hd] at hrest
    simp only [] at hrest
    obtain ⟨hv, hs⟩ := AM.pure_ok hrest
    refine ⟨hs, ?_⟩
    rw [hv]
    exact (denoteCIListGo_spec hok.wf cs (DMemoOK.empty s.store) hd).1

/-! ## The intern direction -/

/-- con-leche: none — the intern memo's invariant: every recorded handle
denotes its key. -/
def EMemoOK (st : EStore) (m : EMemo) : Prop :=
  ∀ e h, m[e]? = some h → denoteE st h = some e

theorem EMemoOK.empty (st : EStore) : EMemoOK st (∅ : EMemo) := by
  intro e h hm; simp at hm

/-- con-leche: none — **the intern is the readback's inverse**: what
`internExpr` returns denotes what it was given, in the store the call leaves
behind, and it is persistent when the scratch tier is closed.

`sorry`: the structural recursion over `ConLeche.Expr`, each arm one
`Bridge/Specs.lean` `internE` face, with `EMemoOK` carried and
`Bridge/Rel.lean`'s `denote_ext` moving the earlier children forward.  The
persistence clause is `intern`'s `scratchOn = false` branch, which
`Arena/WFProofs.lean`'s `intern_view_spec` already exposes.  Task
#97-P3-Frontend's sorry list, item 2. -/
theorem internExpr_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {e : Expr} {h : EIdx}
    (hrun : ConRon.Arena.Frontend.internExpr e s = .ok (h, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ denoteE s'.store h = some e ∧
      PersE h ∧ s'.store.scratchOn = false ∧ s'.memos = s.memos ∧
      s'.caches = s.caches ∧ s'.pins = s.pins := by
  sorry

/-- con-leche: none — the same at a declaration list, which is what the
modeller seam interns.

`sorry`: `internExpr_run` through `internCV` / `internCI` / `internDecl`, list
by list.  Task #97-P3-Frontend's sorry list, item 2. -/
theorem internDecls_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {ds : List Declaration} {hs : List IDeclaration}
    (hrun : internDecls m ds s = .ok ((m', hs), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ denoteDecls s'.store hs = some ds ∧
      (∀ d ∈ hs, PersDecl d) ∧ s'.store.scratchOn = false ∧
      s'.memos = s.memos ∧ s'.caches = s.caches ∧ s'.pins = s.pins := by
  sorry

/-! ## The seam's two readbacks

`Arena/Frontend/InModel.lean` reads the block and builds con-leche's `Ctx` out
of three closures; these two equations are what
`Bridge/Frontend/Modeller.lean`'s `inProcessModeller_refines` composes. -/

/-- con-leche: none — the block the seam reads back is the block the relation
names.

`sorry`: `denoteCVGo_spec` through the three member families, then
`BlockRecRel`'s three `Forall₂` clauses.  Task #97-P3-Frontend's sorry list,
item 1. -/
theorem denoteBlockRec_eq_of_rel {st : EStore} (hwf : StoreWF st) {b : BlockRec}
    {bP : ConLeche.Frontend.InModel.BlockRec} (h : BlockRecRel st b bP) :
    denoteBlockRec st b = some bP := by
  sorry

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:119-124 Ctx — the context
the seam builds IS the context the relation names.  Function extensionality at
three fields, each of which probes the name store with `nameHandle?` where the
relation quantifies over handles that denote — and the two meet because
`denoteN` is injective (DESIGN §8.3's soundness obligation).

`sorry`: `nameHandle?`'s own exactness (`NStore.find?` at a name that was
interned) plus `denoteN_inj`, then `denoteEShared_eq_denoteE` at the `tbl`
field and `denoteBlockRec_eq_of_rel` at the `blocks` one.  Task
#97-P3-Frontend's sorry list, item 3. -/
theorem ctxOf_eq_of_rel {st : EStore} (hwf : StoreWF st) {c : Ctx}
    {cc : ConLeche.Frontend.InModel.Ctx} (h : CtxRel st c cc) :
    ctxOf st c = cc := by
  sorry

end ConRon.Bridge.Frontend
