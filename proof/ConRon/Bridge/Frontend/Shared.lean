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
import ConRon.Bridge.SpecsL
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

The rank induction of `Arena/WFProofs.lean`, run at `denoteEGo` instead of at
`denoteE`: `EWFAt.childOK` gives `rk c < rk i` at every expression child, and
`rankP`/`rankS` put `rk h` under the store's node count — which is exactly the
fuel `denoteEShared` calls at. -/
theorem denoteEGo_isSome {st : EStore} {rk : EIdx → Nat} (hwf : EWFAt st rk) :
    ∀ (fuel : Nat) {m : DMemo}, DMemoOK st m → ∀ {h : EIdx} {e : Expr},
      denoteE st h = some e → rk h < fuel →
        ∃ m', denoteEGo st m fuel h = some (m', e) ∧ DMemoOK st m' := by
  intro fuel
  induction fuel with
  | zero => intro m hm h e hd hr; omega
  | succ f ih =>
    intro m hm h e hd hr
    rw [denoteEGo]
    cases hmem : m[h]? with
    | some x =>
      have : x = e := by rw [hm h x hmem] at hd; exact (Option.some.injEq _ _ ▸ hd)
      subst this
      exact ⟨m, rfl, hm⟩
    | none =>
    -- the node has a view, because its denotation does
    obtain ⟨v, hv⟩ : ∃ v, st.view h = some v := by
      simp only [denoteE, denoteEAux, Option.bind_eq_some_iff] at hd
      obtain ⟨v, hv, -⟩ := hd
      exact ⟨v, hv⟩
    have hun : denoteEView st v = some e := by
      rw [← denoteE_unfold hwf hv]; exact hd
    have hch : ∀ c ∈ v.echildren, rk c < f := by
      intro c hc
      have := (hwf.childOK h v hv c hc).2.1
      omega
    cases v with
    | bvar k =>
      simp only [hv]
      simp only [denoteEView, Option.some.injEq] at hun
      subst hun
      exact ⟨m.insert h (Expr.bvar k), rfl, hm.insert (by rw [hd])⟩
    | lit l =>
      simp only [hv]
      simp only [denoteEView, Option.some.injEq] at hun
      subst hun
      exact ⟨m.insert h (Expr.lit l), rfl, hm.insert (by rw [hd])⟩
    | sort u =>
      simp only [hv]
      simp only [denoteEView, Option.map_eq_some_iff] at hun
      obtain ⟨l, hl, he⟩ := hun
      subst he
      exact ⟨m.insert h (Expr.sort l), by rw [hl], hm.insert (by rw [hd])⟩
    | const n us =>
      simp only [hv]
      simp only [denoteEView, opt2_eq_some_iff] at hun
      obtain ⟨nm, ls, hn, hls, he⟩ := hun
      subst he
      exact ⟨m.insert h (Expr.const nm ls), by rw [hn, hls], hm.insert (by rw [hd])⟩
    | fvar k ty =>
      simp only [hv]
      simp only [denoteEView, Option.map_eq_some_iff] at hun
      obtain ⟨t, ht, he⟩ := hun
      obtain ⟨m1, h1, hm1⟩ :=
        ih hm ht (hch ty (by simp [ENodeView.echildren]))
      subst he
      exact ⟨m1.insert h (Expr.fvar k t), by rw [h1], hm1.insert (by rw [hd])⟩
    | app g a =>
      simp only [hv]
      simp only [denoteEView, opt2_eq_some_iff] at hun
      obtain ⟨ef, ea, hf, ha, he⟩ := hun
      obtain ⟨m1, h1, hm1⟩ := ih hm hf (hch g (by simp [ENodeView.echildren]))
      obtain ⟨m2, h2, hm2⟩ := ih hm1 ha (hch a (by simp [ENodeView.echildren]))
      subst he
      exact ⟨m2.insert h (Expr.app ef ea), by rw [h1]; simp only []; rw [h2],
        hm2.insert (by rw [hd])⟩
    | lam ty b bi =>
      simp only [hv]
      simp only [denoteEView, opt2_eq_some_iff] at hun
      obtain ⟨et, eb, ht, hb, he⟩ := hun
      obtain ⟨m1, h1, hm1⟩ := ih hm ht (hch ty (by simp [ENodeView.echildren]))
      obtain ⟨m2, h2, hm2⟩ := ih hm1 hb (hch b (by simp [ENodeView.echildren]))
      subst he
      exact ⟨m2.insert h (Expr.lam et eb bi), by rw [h1]; simp only []; rw [h2],
        hm2.insert (by rw [hd])⟩
    | forallE ty b bi =>
      simp only [hv]
      simp only [denoteEView, opt2_eq_some_iff] at hun
      obtain ⟨et, eb, ht, hb, he⟩ := hun
      obtain ⟨m1, h1, hm1⟩ := ih hm ht (hch ty (by simp [ENodeView.echildren]))
      obtain ⟨m2, h2, hm2⟩ := ih hm1 hb (hch b (by simp [ENodeView.echildren]))
      subst he
      exact ⟨m2.insert h (Expr.forallE et eb bi),
        by rw [h1]; simp only []; rw [h2], hm2.insert (by rw [hd])⟩
    | letE ty w b =>
      simp only [hv]
      simp only [denoteEView, opt3] at hun
      split at hun
      · rename_i et ev eb ht hw hb
        simp only [Option.some.injEq] at hun
        obtain ⟨m1, h1, hm1⟩ := ih hm ht (hch ty (by simp [ENodeView.echildren]))
        obtain ⟨m2, h2, hm2⟩ := ih hm1 hw (hch w (by simp [ENodeView.echildren]))
        obtain ⟨m3, h3, hm3⟩ := ih hm2 hb (hch b (by simp [ENodeView.echildren]))
        subst hun
        exact ⟨m3.insert h (Expr.letE et ev eb),
          by rw [h1]; simp only []; rw [h2]; simp only []; rw [h3],
          hm3.insert (by rw [hd])⟩
      · exact absurd hun (by simp)
    | proj n i sub =>
      simp only [hv]
      simp only [denoteEView, opt2_eq_some_iff] at hun
      obtain ⟨nm, es, hn, hs, he⟩ := hun
      obtain ⟨m1, h1, hm1⟩ := ih hm hs (hch sub (by simp [ENodeView.echildren]))
      subst he
      exact ⟨m1.insert h (Expr.proj nm i es), by rw [hn, h1],
        hm1.insert (by rw [hd])⟩

/-- con-leche: none — the other half of the same equation: a handle that
denotes reads back.  The store's node count bounds every path through it (a
child is interned before its parent), which is `storeFuel`'s own justification
in `Arena/Frontend/ExportC.lean`. -/
theorem denoteEShared_isSome {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} (hd : denoteE st h = some e) : denoteEShared st h = some e := by
  obtain ⟨rk, hwf'⟩ := hwf
  have hvs : (st.view h).isSome = true := by
    simp only [denoteE, denoteEAux, Option.bind_eq_some_iff] at hd
    obtain ⟨v, hv, -⟩ := hd
    rw [hv]; rfl
  have hrank : rk h < st.nodeCount + 1 := by
    by_cases hp : h.isPersistent = true
    · have := hwf'.rankP h hp hvs
      simp only [EStore.nodeCount]
      omega
    · have := hwf'.rankS h (by simpa using hp) hvs
      omega
  obtain ⟨m', hgo, -⟩ :=
    denoteEGo_isSome hwf' (st.nodeCount + 1) (DMemoOK.empty st) hd hrank
  simp only [denoteEShared, hgo]

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

theorem EMemoOK.mono {st st' : EStore} {m : EMemo} (h : EMemoOK st m)
    (hx : Ext st st') : EMemoOK st' m :=
  fun e i hi => denote_ext (h e i hi) hx

theorem EMemoOK.insert {st : EStore} {m : EMemo} (hm : EMemoOK st m)
    {e : Expr} {i : EIdx} (hd : denoteE st i = some e) :
    EMemoOK st (m.insert e i) := by
  intro k x hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i heq
    obtain rfl : e = k := by simpa using heq
    simp only [Option.some.injEq] at hk
    subst hk; exact hd
  · exact hm k x hk

/-! ## The intern direction's frame -/

structure IStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  off : s'.store.scratchOn = false
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem IStep.refl {s : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) : IStep s s :=
  ⟨hok, Ext.refl _, hoff, rfl, rfl, rfl⟩

theorem IStep.trans {a b c : AState} (h₁ : IStep a b) (h₂ : IStep b c) :
    IStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, h₂.off, by rw [h₂.memos, h₁.memos],
    by rw [h₂.caches, h₁.caches], by rw [h₂.pins, h₁.pins]⟩

theorem IStep.toParse {s s' : AState} (h : IStep s s')
    (hoff : s.store.scratchOn = false) : ParseStep s s' :=
  ParseStep.of_caches h.ok h.ext (by rw [h.off, hoff]) h.memos h.caches h.pins

/-! ## `internE`'s scratch flag -/

theorem AM.set_state_ok {s s' t : AState} {u : PUnit}
    (h : (set t : AM PUnit) s = .ok (u, s')) : s' = t := by
  have he : ((PUnit.unit, t) : PUnit × AState) = (u, s') := Except.ok.inj h
  exact (congrArg Prod.snd he).symm

theorem internE_scratchOn {s s' : AState} {v : ENodeView} {h : EIdx}
    (hrun : internE v s = .ok (h, s')) :
    s'.store.scratchOn = s.store.scratchOn := by
  rw [internE] at hrun
  obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
  obtain ⟨ht, hs₁⟩ := AM.get_ok hget
  rw [ht, hs₁] at hrest
  cases hf : s.store.find? v with
  | some i => rw [hf] at hrest; rw [(AM.pure_ok hrest).2]
  | none =>
    rw [hf] at hrest
    simp only [] at hrest
    repeat' split at hrest
    all_goals
      first
        | exact absurd (AM.fail_ok hrest) (by simp)
        | (obtain ⟨u, s₂, hset, hrest2⟩ := AM.bind_ok hrest
           rw [(AM.pure_ok hrest2).2, AM.set_state_ok hset]
           exact EStore.scratchOn_intern _ _)

/-! ## The four leaf interns, in run form -/

theorem internE_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {v : ENodeView} (hv : s.store.ViewOK v)
    {h : EIdx} (hrun : internE v s = .ok (h, s')) :
    IStep s s' ∧ PersE h ∧ denoteE s'.store h = denoteEView s'.store v := by
  obtain ⟨hwf, hx, -, -, -, hm, hc, hp, hview, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internE_spec s v hok.wf hv)
  have hon : s'.store.scratchOn = false := by
    rw [internE_scratchOn hrun]; exact hoff
  exact ⟨⟨⟨hwf⟩, hx, hon, hm, hc, hp⟩, PersE_of_view hwf hon hview, hden⟩

theorem internName_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {nm : ConLeche.Name} {h : NIdx}
    (hrun : ConRon.Arena.internName nm s = .ok (h, s')) :
    IStep s s' ∧ PersN h ∧ denoteN s'.store.ns h = some nm := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internName_spec s nm hok.wf)
  have hon' : s'.store.scratchOn = false := by rw [hon]; exact hoff
  obtain ⟨w, hw⟩ := Arena.denoteN_view hden
  exact ⟨⟨⟨hwf⟩, hx, hon', hm, hc, hp⟩, PersN_of_view hwf hon' hw, hden⟩

theorem internLevel_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {u : Level} {h : LIdx}
    (hrun : ConRon.Arena.internLevel u s = .ok (h, s')) :
    IStep s s' ∧ PersL h ∧ denoteL s'.store.ls h = some u := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLevel_spec s u hok.wf)
  have hon' : s'.store.scratchOn = false := by rw [hon]; exact hoff
  obtain ⟨w, hw⟩ := Arena.denoteL_view hden
  exact ⟨⟨⟨hwf⟩, hx, hon', hm, hc, hp⟩, PersL_of_view hwf hon' hw, hden⟩

theorem internLevels_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {us : List Level} {h : LsIdx}
    (hrun : ConRon.Arena.internLevels us s = .ok (h, s')) :
    IStep s s' ∧ denoteLs s'.store.lss h = some us := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internLevels_spec s us hok.wf)
  exact ⟨⟨⟨hwf⟩, hx, by rw [hon]; exact hoff, hm, hc, hp⟩, hden⟩

/-! ## Two handle lists -/

theorem internNameList_istep : ∀ (ns : List ConLeche.Name) {s s' : AState}
    {hs : List NIdx}, StateOK s → s.store.scratchOn = false →
    ConRon.Arena.Frontend.internNameList ns s = .ok (hs, s') →
    IStep s s' ∧ PersNList hs ∧ denoteNList s'.store.ns hs = some ns := by
  intro ns
  induction ns with
  | nil =>
    intro s s' hs hok hoff hrun
    rw [ConRon.Arena.Frontend.internNameList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst; subst hv
    exact ⟨IStep.refl hok hoff, by intro n hn; simp at hn, rfl⟩
  | cons a as ih =>
    intro s s' hs hok hoff hrun
    rw [ConRon.Arena.Frontend.internNameList] at hrun
    obtain ⟨h1, s₁, hn, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hpn, hdn⟩ := internName_istep hok hoff hn
    obtain ⟨t1, s₂, hns, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hpns, hdns⟩ := ih hstep1.ok hstep1.off hns
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst; subst hv
    refine ⟨hstep1.trans hstep2, ?_, ?_⟩
    · intro n hn'
      simp only [List.mem_cons] at hn'
      rcases hn' with rfl | hn'
      · exact hpn
      · exact hpns n hn'
    · simp only [denoteNList, denoteN_ext hdn hstep2.ext, hdns]

theorem internLevelList_istep : ∀ (us : List Level) {s s' : AState}
    {hs : List LIdx}, StateOK s → s.store.scratchOn = false →
    ConRon.Arena.internLevelList us s = .ok (hs, s') →
    IStep s s' ∧ PersLList hs ∧ denoteLList s'.store.ls hs = some us := by
  intro us
  induction us with
  | nil =>
    intro s s' hs hok hoff hrun
    rw [ConRon.Arena.internLevelList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst; subst hv
    exact ⟨IStep.refl hok hoff, by intro u hu; simp at hu, rfl⟩
  | cons a as ih =>
    intro s s' hs hok hoff hrun
    rw [ConRon.Arena.internLevelList] at hrun
    obtain ⟨h1, s₁, hl, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hpl, hdl⟩ := internLevel_istep hok hoff hl
    obtain ⟨t1, s₂, hls, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hpls, hdls⟩ := ih hstep1.ok hstep1.off hls
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst; subst hv
    refine ⟨hstep1.trans hstep2, ?_, ?_⟩
    · intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact hpl
      · exact hpls u hu
    · simp only [denoteLList, opt2_eq_some_iff]
      exact ⟨a, as, denoteL_ext hdl hstep2.ext, hdls, rfl⟩

/-! ## The expression intern, arm by arm -/

theorem internExprGo_istep :
    ∀ (e : Expr) {s s' : AState} {m m' : EMemo} {h : EIdx},
      StateOK s → s.store.scratchOn = false → EMemoOK s.store m →
      internExprGo m e s = .ok ((m', h), s') →
      IStep s s' ∧ PersE h ∧ denoteE s'.store h = some e ∧
        EMemoOK s'.store m' := by
  intro e
  induction e with
  | bvar i =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    obtain ⟨x, s₁, hin, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    obtain ⟨hstep1, hpe, hden⟩ := internE_istep hok hoff viewOK_bvar hin
    exact ⟨hstep1, hpe, by rw [hden]; rfl, hm.mono hstep1.ext⟩
  | lit l =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    obtain ⟨x, s₁, hin, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    obtain ⟨hstep1, hpe, hden⟩ := internE_istep hok hoff viewOK_lit hin
    exact ⟨hstep1, hpe, by rw [hden]; rfl, hm.mono hstep1.ext⟩
  | sort u =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    obtain ⟨lu, s₁, hl, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hpl, hdl⟩ := internLevel_istep hok hoff hl
    obtain ⟨x, s₂, hin, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hpe, hden⟩ :=
      internE_istep hstep1.ok hstep1.off
        (viewOK_sort (lview_isSome_of_denote hdl)) hin
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    refine ⟨hstep1.trans hstep2, hpe, ?_,
      (hm.mono hstep1.ext).mono hstep2.ext⟩
    rw [hden]
    simp only [denoteEView, denoteL_ext hdl hstep2.ext, Option.map_some]
  | const n us =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    obtain ⟨hn, s₁, hnm, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hpn, hdn⟩ := internName_istep hok hoff hnm
    obtain ⟨hus, s₂, hls, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdls⟩ := internLevels_istep hstep1.ok hstep1.off hls
    obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hstep3, hpe, hden⟩ :=
      internE_istep hstep2.ok hstep2.off
        (viewOK_const (nview_isSome_of_denote (denoteN_ext hdn hstep2.ext))
          (by obtain ⟨w, hw, -⟩ := Arena.denoteLs_view hdls; rw [hw]; rfl)) hin
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    refine ⟨(hstep1.trans hstep2).trans hstep3, hpe, ?_,
      ((hm.mono hstep1.ext).mono hstep2.ext).mono hstep3.ext⟩
    rw [hden]
    simp only [denoteEView, opt2_eq_some_iff]
    exact ⟨n, us, denoteN_ext hdn (hstep2.ext.trans hstep3.ext),
      hstep3.ext.lss.lst hus us hdls, rfl⟩
  | fvar i ty ih =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.fvar i ty]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStep.refl hok hoff, PersE_of_view hok.wf hoff hw, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, t1⟩ := p1
      obtain ⟨hstep1, hpt, hdt, hm1⟩ := ih hok hoff hm h1
      simp only [] at hrest
      obtain ⟨x, s₂, hin, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨hstep2, hpe, hden⟩ :=
        internE_istep hstep1.ok hstep1.off (viewOK_fvar (by rw [hdt]; rfl)) hin
      have hde : denoteE s₂.store x = some (Expr.fvar i ty) := by
        rw [hden]
        simp only [denoteEView, denote_ext hdt hstep2.ext, Option.map_some]
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨hstep1.trans hstep2, hpe, hde,
        (hm1.mono hstep2.ext).insert hde⟩
  | app f a ihf iha =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.app f a]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStep.refl hok hoff, PersE_of_view hok.wf hoff hw, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, hf⟩ := p1
      obtain ⟨hstep1, hpf, hdf, hm1⟩ := ihf hok hoff hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, ha⟩ := p2
      obtain ⟨hstep2, hpa, hda, hm2⟩ := iha hstep1.ok hstep1.off hm1 h2
      simp only [] at hrest2
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hpe, hden⟩ :=
        internE_istep hstep2.ok hstep2.off
          (viewOK_app (by rw [denote_ext hdf hstep2.ext]; rfl)
            (by rw [hda]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.app f a) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨f, a, denote_ext hdf (hstep2.ext.trans hstep3.ext),
          denote_ext hda hstep3.ext, rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hpe, hde,
        (hm2.mono hstep3.ext).insert hde⟩
  | lam ty b bi ihty ihb =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.lam ty b bi]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStep.refl hok hoff, PersE_of_view hok.wf hoff hw, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, ht⟩ := p1
      obtain ⟨hstep1, hpt, hdt, hm1⟩ := ihty hok hoff hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, hb⟩ := p2
      obtain ⟨hstep2, hpb, hdb, hm2⟩ := ihb hstep1.ok hstep1.off hm1 h2
      simp only [] at hrest2
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hpe, hden⟩ :=
        internE_istep hstep2.ok hstep2.off
          (viewOK_lam (by rw [denote_ext hdt hstep2.ext]; rfl)
            (by rw [hdb]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.lam ty b bi) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨ty, b, denote_ext hdt (hstep2.ext.trans hstep3.ext),
          denote_ext hdb hstep3.ext, rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hpe, hde,
        (hm2.mono hstep3.ext).insert hde⟩
  | forallE ty b bi ihty ihb =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.forallE ty b bi]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStep.refl hok hoff, PersE_of_view hok.wf hoff hw, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, ht⟩ := p1
      obtain ⟨hstep1, hpt, hdt, hm1⟩ := ihty hok hoff hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, hb⟩ := p2
      obtain ⟨hstep2, hpb, hdb, hm2⟩ := ihb hstep1.ok hstep1.off hm1 h2
      simp only [] at hrest2
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hpe, hden⟩ :=
        internE_istep hstep2.ok hstep2.off
          (viewOK_forallE (by rw [denote_ext hdt hstep2.ext]; rfl)
            (by rw [hdb]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.forallE ty b bi) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨ty, b, denote_ext hdt (hstep2.ext.trans hstep3.ext),
          denote_ext hdb hstep3.ext, rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hpe, hde,
        (hm2.mono hstep3.ext).insert hde⟩
  | letE ty v b ihty ihv ihb =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.letE ty v b]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv', hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv'
      obtain ⟨hmm, hhh⟩ := hv'
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStep.refl hok hoff, PersE_of_view hok.wf hoff hw, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, ht⟩ := p1
      obtain ⟨hstep1, hpt, hdt, hm1⟩ := ihty hok hoff hm h1
      simp only [] at hrest
      obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨m2, hvv⟩ := p2
      obtain ⟨hstep2, hpv, hdv, hm2⟩ := ihv hstep1.ok hstep1.off hm1 h2
      simp only [] at hrest2
      obtain ⟨p3, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨m3, hb⟩ := p3
      obtain ⟨hstep3, hpb, hdb, hm3⟩ := ihb hstep2.ok hstep2.off hm2 h3
      simp only [] at hrest3
      obtain ⟨x, s₄, hin, hrest4⟩ := AM.bind_ok hrest3
      obtain ⟨hstep4, hpe, hden⟩ :=
        internE_istep hstep3.ok hstep3.off
          (viewOK_letE
            (by rw [denote_ext hdt (hstep2.ext.trans hstep3.ext)]; rfl)
            (by rw [denote_ext hdv hstep3.ext]; rfl) (by rw [hdb]; rfl)) hin
      have hde : denoteE s₄.store x = some (Expr.letE ty v b) := by
        rw [hden]
        simp only [denoteEView, opt3_eq_some_iff]
        exact ⟨ty, v, b,
          denote_ext hdt ((hstep2.ext.trans hstep3.ext).trans hstep4.ext),
          denote_ext hdv (hstep3.ext.trans hstep4.ext),
          denote_ext hdb hstep4.ext, rfl⟩
      obtain ⟨hv', hst⟩ := AM.pure_ok hrest4
      subst hst
      simp only [Prod.mk.injEq] at hv'
      obtain ⟨hmm, hhh⟩ := hv'
      subst hmm; subst hhh
      exact ⟨((hstep1.trans hstep2).trans hstep3).trans hstep4, hpe, hde,
        (hm3.mono hstep4.ext).insert hde⟩
  | proj n i sub ih =>
    intro s s' m m' h hok hoff hm hrun
    rw [internExprGo] at hrun
    cases hmem : m[Expr.proj n i sub]? with
    | some hh =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨hv, hst⟩ := AM.pure_ok hrun
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      have hd := hm _ _ hmem
      obtain ⟨w, hw⟩ := Arena.denoteE_view hd
      exact ⟨IStep.refl hok hoff, PersE_of_view hok.wf hoff hw, hd, hm⟩
    | none =>
      rw [hmem] at hrun
      simp only [] at hrun
      obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
      obtain ⟨m1, hsu⟩ := p1
      obtain ⟨hstep1, hps, hds, hm1⟩ := ih hok hoff hm h1
      simp only [] at hrest
      obtain ⟨hn, s₂, hnm, hrest2⟩ := AM.bind_ok hrest
      obtain ⟨hstep2, hpn, hdn⟩ := internName_istep hstep1.ok hstep1.off hnm
      obtain ⟨x, s₃, hin, hrest3⟩ := AM.bind_ok hrest2
      obtain ⟨hstep3, hpe, hden⟩ :=
        internE_istep hstep2.ok hstep2.off
          (viewOK_proj (nview_isSome_of_denote hdn)
            (by rw [denote_ext hds hstep2.ext]; rfl)) hin
      have hde : denoteE s₃.store x = some (Expr.proj n i sub) := by
        rw [hden]
        simp only [denoteEView, opt2_eq_some_iff]
        exact ⟨n, sub, denoteN_ext hdn hstep3.ext,
          denote_ext hds (hstep2.ext.trans hstep3.ext), rfl⟩
      obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
      subst hst
      simp only [Prod.mk.injEq] at hv
      obtain ⟨hmm, hhh⟩ := hv
      subst hmm; subst hhh
      exact ⟨(hstep1.trans hstep2).trans hstep3, hpe, hde,
        (hm1.mono (hstep2.ext.trans hstep3.ext)).insert hde⟩

theorem internExprList_istep : ∀ (es : List Expr) {s s' : AState}
    {m m' : EMemo} {hs : List EIdx}, StateOK s → s.store.scratchOn = false →
    EMemoOK s.store m → ConRon.Arena.Frontend.internExprList m es s = .ok ((m', hs), s') →
    IStep s s' ∧ PersEList hs ∧ denoteEList s'.store hs = some es ∧
      EMemoOK s'.store m' := by
  intro es
  induction es with
  | nil =>
    intro s s' m m' hs hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internExprList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    exact ⟨IStep.refl hok hoff, by intro x hx; simp at hx, rfl, hm⟩
  | cons e es ih =>
    intro s s' m m' hs hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internExprList] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, x1⟩ := p1
    obtain ⟨hstep1, hpe, hde, hm1⟩ := internExprGo_istep e hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, xs⟩ := p2
    obtain ⟨hstep2, hpes, hdes, hm2⟩ :=
      ih hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hhh⟩ := hv
    subst hmm; subst hhh
    refine ⟨hstep1.trans hstep2, ?_, ?_, hm2⟩
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hpe
      · exact hpes x hx
    · simp only [denoteEList, denote_ext hde hstep2.ext, hdes]

/-! ## The reserved projection-table name -/

theorem internNNode_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {v : NNodeView}
    (hv : s.store.ns.ViewOK v) {h : NIdx}
    (hrun : internNNode v s = .ok (h, s')) :
    IStep s s' ∧ PersN h ∧
      denoteN s'.store.ns h = denoteNView s'.store.ns v := by
  obtain ⟨hwf, hx, -, -, hon, hm, hc, hp, hview, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internNNode_spec s v hok.wf hv)
  have hon' : s'.store.scratchOn = false := by rw [hon]; exact hoff
  exact ⟨⟨⟨hwf⟩, hx, hon', hm, hc, hp⟩, PersN_of_view hwf hon' hview, hden⟩

theorem projTableName_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {T : NIdx} {Tn : ConLeche.Name}
    (hT : denoteN s.store.ns T = some Tn) {h : NIdx}
    (hrun : ConRon.Arena.projTableName T s = .ok (h, s')) :
    IStep s s' ∧ PersN h := by
  rw [ConRon.Arena.projTableName] at hrun
  obtain ⟨a, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hpa, hda⟩ :=
    internNNode_istep hok hoff
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc; exact nview_isSome_of_denote hT) h1
  have hda' : (s₁.store.ns.view a).isSome = true := by
    obtain ⟨w, hw⟩ := Arena.denoteN_view
      (show denoteN s₁.store.ns a = some (Tn.str "projTable") by
        rw [hda]; simp only [denoteNView, denoteN_ext hT hstep1.ext,
          Option.map_some])
    rw [hw]; rfl
  obtain ⟨hstep2, hpb, -⟩ :=
    internNNode_istep hstep1.ok hstep1.off
      (by intro c hc
          simp only [NNodeView.children, List.mem_singleton] at hc
          subst hc; exact hda') hrest
  exact ⟨hstep1.trans hstep2, hpb⟩

/-! ## The record layers -/

theorem internCV_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {cv : ConstantVal} {icv : IConstantVal}
    (hrun : internCV m cv s = .ok ((m', icv), s')) :
    IStep s s' ∧ PersCV icv ∧ denoteCV s'.store icv = some cv ∧
      EMemoOK s'.store m' := by
  rw [ConRon.Arena.Frontend.internCV] at hrun
  obtain ⟨hn, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hpn, hdn⟩ := internName_istep hok hoff h1
  obtain ⟨hlps, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hstep2, hplps, hdlps⟩ :=
    internNameList_istep cv.levelParams hstep1.ok hstep1.off h2
  obtain ⟨p3, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨m3, hty⟩ := p3
  obtain ⟨hstep3, hpty, hdty, hm3⟩ :=
    internExprGo_istep cv.type hstep2.ok hstep2.off
      (hm.mono (hstep1.ext.trans hstep2.ext)) h3
  simp only [] at hrest3
  have hd : denoteCV s₃.store ⟨hn, hlps, hty⟩ = some cv := by
    simp only [denoteCV, denoteN_ext hdn (hstep2.ext.trans hstep3.ext),
      denoteNListE_ext hstep3.ext _ _ hdlps, hdty]
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
  subst hst
  simp only [Prod.mk.injEq] at hv
  obtain ⟨hmm, hii⟩ := hv
  subst hmm; subst hii
  exact ⟨(hstep1.trans hstep2).trans hstep3,
    ⟨hpn, hplps, hpty⟩, hd, hm3⟩

theorem internFire_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {f : RecRuleFire} {fi : IRecRuleFire}
    (hrun : internFire m f s = .ok ((m', fi), s')) :
    IStep s s' ∧ PersFire fi ∧ denoteFire s'.store fi = some f ∧
      EMemoOK s'.store m' := by
  cases f with
  | inert =>
    rw [ConRon.Arena.Frontend.internFire] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStep.refl hok hoff, trivial, rfl, hm⟩
  | plain =>
    rw [ConRon.Arena.Frontend.internFire] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStep.refl hok hoff, trivial, rfl, hm⟩
  | nested lvls pins =>
    rw [ConRon.Arena.Frontend.internFire] at hrun
    obtain ⟨hls, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hpls, hdls⟩ := internLevelList_istep lvls hok hoff h1
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, hps⟩ := p2
    obtain ⟨hstep2, hpps, hdps, hm2⟩ :=
      internExprList_istep pins hstep1.ok hstep1.off (hm.mono hstep1.ext) h2
    simp only [] at hrest2
    have hd : denoteFire s₂.store (.nested hls hps) = some (.nested lvls pins) := by
      simp only [denoteFire, denoteLListE_ext hstep2.ext _ _ hdls, hdps]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpls, hpps⟩, hd, hm2⟩

theorem internRule_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {rl : RecRule} {ri : IRecRule}
    (hrun : internRule m rl s = .ok ((m', ri), s')) :
    IStep s s' ∧ PersRule ri ∧ denoteRule s'.store ri = some rl ∧
      EMemoOK s'.store m' := by
  rw [ConRon.Arena.Frontend.internRule] at hrun
  obtain ⟨hc, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hpc, hdc⟩ := internName_istep hok hoff h1
  obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨m2, hf⟩ := p2
  obtain ⟨hstep2, hpf, hdf, hm2⟩ :=
    internFire_istep hstep1.ok hstep1.off (hm.mono hstep1.ext) h2
  simp only [] at hrest2
  obtain ⟨p3, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨m3, hr⟩ := p3
  obtain ⟨hstep3, hpr, hdr, hm3⟩ :=
    internExprGo_istep rl.rhs hstep2.ok hstep2.off hm2 h3
  simp only [] at hrest3
  have hd : denoteRule s₃.store
      ⟨hc, rl.nfields, rl.ctorParams, hf, hr, rl.k, rl.eta, rl.paramsBlind⟩
      = some rl := by
    simp only [denoteRule, denoteN_ext hdc (hstep2.ext.trans hstep3.ext),
      denoteFire_ext hdf hstep3.ext, hdr]
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest3
  subst hst
  simp only [Prod.mk.injEq] at hv
  obtain ⟨hmm, hii⟩ := hv
  subst hmm; subst hii
  exact ⟨(hstep1.trans hstep2).trans hstep3, ⟨hpc, hpf, hpr⟩, hd, hm3⟩

theorem internRules_istep : ∀ (rs : List RecRule) {s s' : AState}
    {m m' : EMemo} {ris : List IRecRule}, StateOK s →
    s.store.scratchOn = false → EMemoOK s.store m →
    internRules m rs s = .ok ((m', ris), s') →
    IStep s s' ∧ PersRules ris ∧ denoteRules s'.store ris = some rs ∧
      EMemoOK s'.store m' := by
  intro rs
  induction rs with
  | nil =>
    intro s s' m m' ris hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internRules] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStep.refl hok hoff, by intro x hx; simp at hx, rfl, hm⟩
  | cons r rs ih =>
    intro s s' m m' ris hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internRules] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, x1⟩ := p1
    obtain ⟨hstep1, hpr, hdr, hm1⟩ := internRule_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, xs⟩ := p2
    obtain ⟨hstep2, hprs, hdrs, hm2⟩ := ih hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteRules s₂.store (x1 :: xs) = some (r :: rs) := by
      simp only [denoteRules, denoteRule_ext hdr hstep2.ext, hdrs]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    refine ⟨hstep1.trans hstep2, ?_, hd, hm2⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hpr
    · exact hprs x hx

theorem internCaps_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {c : IndCaps} {ci : IIndCaps}
    (hrun : internCaps c s = .ok (ci, s')) :
    IStep s s' ∧ PersCaps ci ∧ denoteCaps s'.store ci = some c := by
  rw [ConRon.Arena.Frontend.internCaps] at hrun
  obtain ⟨ct, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hpc, hdc⟩ := internName_istep hok hoff h1
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst; subst hv
  exact ⟨hstep1, hpc, by simp only [denoteCaps, hdc]⟩

theorem internProjTable_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {t : ProjTable} {ti : IProjTable}
    (hrun : internProjTable m t s = .ok ((m', ti), s')) :
    IStep s s' ∧ PersProjTable ti ∧ denoteProjTable s'.store ti = some t ∧
      EMemoOK s'.store m' := by
  rw [ConRon.Arena.Frontend.internProjTable] at hrun
  obtain ⟨sn, s₁, h1, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hpsn, hdsn⟩ := internName_istep hok hoff h1
  obtain ⟨tn, s₂, h2, hrest2⟩ := AM.bind_ok hrest
  obtain ⟨hstep2, hptn⟩ := projTableName_istep hstep1.ok hstep1.off hdsn h2
  obtain ⟨lps, s₃, h3, hrest3⟩ := AM.bind_ok hrest2
  obtain ⟨hstep3, hplps, hdlps⟩ :=
    internNameList_istep t.levelParams hstep2.ok hstep2.off h3
  obtain ⟨cn, s₄, h4, hrest4⟩ := AM.bind_ok hrest3
  obtain ⟨hstep4, hpcn, hdcn⟩ := internName_istep hstep3.ok hstep3.off h4
  obtain ⟨ss, s₅, h5, hrest5⟩ := AM.bind_ok hrest4
  obtain ⟨hstep5, hpss, hdss⟩ := internLevel_istep hstep4.ok hstep4.off h5
  obtain ⟨p6, s₆, h6, hrest6⟩ := AM.bind_ok hrest5
  obtain ⟨m6, bs⟩ := p6
  obtain ⟨hstep6, hpbs, hdbs, hm6⟩ :=
    internExprList_istep t.bodies.toList hstep5.ok hstep5.off
      (hm.mono ((((hstep1.ext.trans hstep2.ext).trans hstep3.ext).trans
        hstep4.ext).trans hstep5.ext)) h6
  simp only [] at hrest6
  obtain ⟨gs, s₇, h7, hrest7⟩ := AM.bind_ok hrest6
  obtain ⟨hstep7, hpgs, hdgs⟩ :=
    internLevelList_istep t.guards hstep6.ok hstep6.off h7
  have hxs : Ext s₃.store s₇.store :=
    ((hstep4.ext.trans hstep5.ext).trans hstep6.ext).trans hstep7.ext
  have hd : denoteProjTable s₇.store
      ⟨sn, tn, lps, t.numParams, cn, t.numFields, ss, bs.toArray, gs, t.off⟩
      = some t := by
    simp only [denoteProjTable,
      denoteN_ext hdsn ((hstep2.ext.trans hstep3.ext).trans hxs),
      denoteNListE_ext hxs _ _ hdlps,
      denoteN_ext hdcn ((hstep5.ext.trans hstep6.ext).trans hstep7.ext),
      denoteL_ext hdss (hstep6.ext.trans hstep7.ext),
      denoteEArray, denoteEList_ext hstep7.ext _ _ hdbs, hdgs]
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest7
  subst hst
  simp only [Prod.mk.injEq] at hv
  obtain ⟨hmm, hii⟩ := hv
  subst hmm; subst hii
  exact ⟨((((((hstep1.trans hstep2).trans hstep3).trans hstep4).trans
      hstep5).trans hstep6).trans hstep7),
    ⟨hpsn, hptn, hplps, hpcn, hpss, by
       simpa only [List.toList_toArray] using hpbs, hpgs⟩,
    hd, hm6.mono hstep7.ext⟩


theorem internCI_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {c : ConstantInfo} {ci : IConstantInfo}
    (hrun : internCI m c s = .ok ((m', ci), s')) :
    IStep s s' ∧ PersCI ci ∧ denoteCI s'.store ci = some c ∧
      EMemoOK s'.store m' := by
  cases c with
  | axiomInfo v =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, hpcv, by simp only [denoteCI, hdcv, Option.map_some], hm1⟩
  | ctorInfo v nP nF =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, hpcv, by simp only [denoteCI, hdcv, Option.map_some], hm1⟩
  | defnInfo v e hh =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, x⟩ := p2
    obtain ⟨hstep2, hpx, hdx, hm2⟩ :=
      internExprGo_istep e hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteCI s₂.store (.defnInfo cv x hh) = some (.defnInfo v e hh) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdx]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpcv, hpx⟩, hd, hm2⟩
  | thmInfo v e =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, x⟩ := p2
    obtain ⟨hstep2, hpx, hdx, hm2⟩ :=
      internExprGo_istep e hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteCI s₂.store (.thmInfo cv x) = some (.thmInfo v e) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdx]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpcv, hpx⟩, hd, hm2⟩
  | indInfo v cps =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨caps, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hpcaps, hdcaps⟩ :=
      internCaps_istep hstep1.ok hstep1.off h2
    have hd : denoteCI s₂.store (.indInfo cv caps) = some (.indInfo v cps) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdcaps]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpcv, hpcaps⟩, hd, hm1.mono hstep2.ext⟩
  | recInfo v mI rP rs =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, rules⟩ := p2
    obtain ⟨hstep2, hprs, hdrs, hm2⟩ :=
      internRules_istep rs hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteCI s₂.store (.recInfo cv mI rP rules)
        = some (.recInfo v mI rP rs) := by
      simp only [denoteCI, denoteCV_ext hdcv hstep2.ext, hdrs]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpcv, hprs⟩, hd, hm2⟩
  | projInfo t =>
    rw [ConRon.Arena.Frontend.internCI] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, tbl⟩ := p1
    obtain ⟨hstep1, hpt, hdt, hm1⟩ := internProjTable_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, hpt, by simp only [denoteCI, hdt, Option.map_some], hm1⟩

theorem internCIList_istep : ∀ (cs : List ConstantInfo) {s s' : AState}
    {m m' : EMemo} {cis : List IConstantInfo}, StateOK s →
    s.store.scratchOn = false → EMemoOK s.store m →
    internCIList m cs s = .ok ((m', cis), s') →
    IStep s s' ∧ PersCIList cis ∧ denoteCIList s'.store cis = some cs ∧
      EMemoOK s'.store m' := by
  intro cs
  induction cs with
  | nil =>
    intro s s' m m' cis hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internCIList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStep.refl hok hoff, by intro x hx; simp at hx, rfl, hm⟩
  | cons c cs ih =>
    intro s s' m m' cis hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internCIList] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, x1⟩ := p1
    obtain ⟨hstep1, hpc, hdc, hm1⟩ := internCI_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, xs⟩ := p2
    obtain ⟨hstep2, hpcs, hdcs, hm2⟩ := ih hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteCIList s₂.store (x1 :: xs) = some (c :: cs) := by
      simp only [denoteCIList, denoteCI_ext hdc hstep2.ext, hdcs]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    refine ⟨hstep1.trans hstep2, ?_, hd, hm2⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hpc
    · exact hpcs x hx

theorem internDecl_istep {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {d : Declaration} {di : IDeclaration}
    (hrun : internDecl m d s = .ok ((m', di), s')) :
    IStep s s' ∧ PersDecl di ∧ denoteDecl s'.store di = some d ∧
      EMemoOK s'.store m' := by
  cases d with
  | basisDecl k =>
    rw [ConRon.Arena.Frontend.internDecl] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStep.refl hok hoff, trivial, rfl, hm⟩
  | axiomDecl v =>
    rw [ConRon.Arena.Frontend.internDecl] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, hpcv, by simp only [denoteDecl, hdcv, Option.map_some], hm1⟩
  | quotDecl k v =>
    rw [ConRon.Arena.Frontend.internDecl] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, hpcv, by simp only [denoteDecl, hdcv, Option.map_some], hm1⟩
  | defnDecl v e hh =>
    rw [ConRon.Arena.Frontend.internDecl] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, x⟩ := p2
    obtain ⟨hstep2, hpx, hdx, hm2⟩ :=
      internExprGo_istep e hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteDecl s₂.store (.defnDecl cv x hh)
        = some (.defnDecl v e hh) := by
      simp only [denoteDecl, denoteCV_ext hdcv hstep2.ext, hdx]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpcv, hpx⟩, hd, hm2⟩
  | thmDecl v e =>
    rw [ConRon.Arena.Frontend.internDecl] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, x⟩ := p2
    obtain ⟨hstep2, hpx, hdx, hm2⟩ :=
      internExprGo_istep e hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteDecl s₂.store (.thmDecl cv x) = some (.thmDecl v e) := by
      simp only [denoteDecl, denoteCV_ext hdcv hstep2.ext, hdx]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpcv, hpx⟩, hd, hm2⟩
  | opaqueDecl v e =>
    rw [ConRon.Arena.Frontend.internDecl] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, cv⟩ := p1
    obtain ⟨hstep1, hpcv, hdcv, hm1⟩ := internCV_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, x⟩ := p2
    obtain ⟨hstep2, hpx, hdx, hm2⟩ :=
      internExprGo_istep e hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : denoteDecl s₂.store (.opaqueDecl cv x)
        = some (.opaqueDecl v e) := by
      simp only [denoteDecl, denoteCV_ext hdcv hstep2.ext, hdx]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1.trans hstep2, ⟨hpcv, hpx⟩, hd, hm2⟩
  | indDecl block nP =>
    rw [ConRon.Arena.Frontend.internDecl] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, b⟩ := p1
    obtain ⟨hstep1, hpb, hdb, hm1⟩ := internCIList_istep block hok hoff hm h1
    simp only [] at hrest
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨hstep1, hpb, by simp only [denoteDecl, hdb, Option.map_some], hm1⟩

theorem internDecls_istep : ∀ (ds : List Declaration) {s s' : AState}
    {m m' : EMemo} {dis : List IDeclaration}, StateOK s →
    s.store.scratchOn = false → EMemoOK s.store m →
    internDecls m ds s = .ok ((m', dis), s') →
    IStep s s' ∧ (∀ d ∈ dis, PersDecl d) ∧
      ConRon.Bridge.denoteDecls s'.store dis = some ds ∧ EMemoOK s'.store m' := by
  intro ds
  induction ds with
  | nil =>
    intro s s' m m' dis hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internDecls] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    exact ⟨IStep.refl hok hoff, by intro x hx; simp at hx, rfl, hm⟩
  | cons d ds ih =>
    intro s s' m m' dis hok hoff hm hrun
    rw [ConRon.Arena.Frontend.internDecls] at hrun
    obtain ⟨p1, s₁, h1, hrest⟩ := AM.bind_ok hrun
    obtain ⟨m1, x1⟩ := p1
    obtain ⟨hstep1, hpd, hdd, hm1⟩ := internDecl_istep hok hoff hm h1
    simp only [] at hrest
    obtain ⟨p2, s₂, h2, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨m2, xs⟩ := p2
    obtain ⟨hstep2, hpds, hdds, hm2⟩ := ih hstep1.ok hstep1.off hm1 h2
    simp only [] at hrest2
    have hd : ConRon.Bridge.denoteDecls s₂.store (x1 :: xs) = some (d :: ds) := by
      simp only [ConRon.Bridge.denoteDecls, denoteDecl_ext hstep2.ext hdd, hdds]
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst
    simp only [Prod.mk.injEq] at hv
    obtain ⟨hmm, hii⟩ := hv
    subst hmm; subst hii
    refine ⟨hstep1.trans hstep2, ?_, hd, hm2⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hpd
    · exact hpds x hx


/-- con-leche: none — **the intern is the readback's inverse**: what
`internExpr` returns denotes what it was given, in the store the call leaves
behind, and it is persistent when the scratch tier is closed.

`internExprGo_istep` at a fresh memo.  The persistence clause is FREE
(`Bridge/Frontend/Rel.lean`'s `PersE_of_view` at the spec's `view` conjunct,
round 2's replacement for finding 9.1). -/
theorem internExpr_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {e : Expr} {h : EIdx}
    (hrun : ConRon.Arena.Frontend.internExpr e s = .ok (h, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ denoteE s'.store h = some e ∧
      PersE h ∧ s'.store.scratchOn = false ∧ s'.memos = s.memos ∧
      s'.caches = s.caches ∧ s'.pins = s.pins := by
  rw [ConRon.Arena.Frontend.internExpr] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨m1, hh⟩ := p
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst; subst hv
  obtain ⟨hstep, hpe, hden, -⟩ :=
    internExprGo_istep e hok hoff (EMemoOK.empty s.store) hgo
  exact ⟨hstep.ok, hstep.ext, hden, hpe, hstep.off, hstep.memos, hstep.caches,
    hstep.pins⟩

/-- con-leche: none — the same at a declaration list, which is what the
modeller seam interns.

`internDecls_istep`, i.e. the twelve record layers above `internExprGo_istep`
composed.  **This was the last blocker of item 8** (`inProcessModeller_wf` /
`_refines`). -/
theorem internDecls_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) {m m' : EMemo} (hm : EMemoOK s.store m)
    {ds : List Declaration} {hs : List IDeclaration}
    (hrun : internDecls m ds s = .ok ((m', hs), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ denoteDecls s'.store hs = some ds ∧
      (∀ d ∈ hs, PersDecl d) ∧ s'.store.scratchOn = false ∧
      s'.memos = s.memos ∧ s'.caches = s.caches ∧ s'.pins = s.pins := by
  obtain ⟨hstep, hpers, hden, -⟩ := internDecls_istep ds hok hoff hm hrun
  exact ⟨hstep.ok, hstep.ext, hden, hpers, hstep.off, hstep.memos,
    hstep.caches, hstep.pins⟩

/-! ## The seam's two readbacks

`Arena/Frontend/InModel.lean` reads the block and builds con-leche's `Ctx` out
of three closures; these two equations are what
`Bridge/Frontend/Modeller.lean`'s `inProcessModeller_refines` composes. -/

/-! ### The readback's existence direction, at the record layers

`denoteEGo_isSome` is the leaf; each layer above it is the same three lines
(destructure the plain denotation, apply the layer below, rebuild). -/

/-- con-leche: none — `denoteEGo_isSome` at the fuel `denoteEShared` and every
record layer call it at. -/
theorem denoteEGo_isSome' {st : EStore} (hwf : StoreWF st) {m : DMemo}
    (hm : DMemoOK st m) {h : EIdx} {e : Expr} (hd : denoteE st h = some e) :
    ∃ m', denoteEGo st m (st.nodeCount + 1) h = some (m', e) ∧ DMemoOK st m' := by
  obtain ⟨rk, hwf'⟩ := hwf
  have hvs : (st.view h).isSome = true := by
    simp only [denoteE, denoteEAux, Option.bind_eq_some_iff] at hd
    obtain ⟨v, hv, -⟩ := hd
    rw [hv]; rfl
  have hrank : rk h < st.nodeCount + 1 := by
    by_cases hp : h.isPersistent = true
    · have := hwf'.rankP h hp hvs
      simp only [EStore.nodeCount]
      omega
    · have := hwf'.rankS h (by simpa using hp) hvs
      omega
  exact denoteEGo_isSome hwf' (st.nodeCount + 1) hm hd hrank

/-- con-leche: none — the `ConstantVal` layer. -/
theorem denoteCVGo_isSome {st : EStore} (hwf : StoreWF st) {m : DMemo}
    (hm : DMemoOK st m) {cv : IConstantVal} {c : ConstantVal}
    (hd : denoteCV st cv = some c) :
    ∃ m', denoteCVGo st m cv = some (m', c) ∧ DMemoOK st m' := by
  rw [denoteCV] at hd
  cases hn : denoteN st.ns cv.name with
  | none => rw [hn] at hd; simp at hd
  | some n =>
  cases hlp : denoteNList st.ns cv.levelParams with
  | none => rw [hn, hlp] at hd; simp at hd
  | some lps =>
  cases ht : denoteE st cv.type with
  | none => rw [hn, hlp, ht] at hd; simp at hd
  | some ty =>
  rw [hn, hlp, ht] at hd
  simp only [Option.some.injEq] at hd
  obtain ⟨m1, h1, hm1⟩ := denoteEGo_isSome' hwf hm ht
  exact ⟨m1, by rw [denoteCVGo, hn, hlp, h1]; simp only []; rw [hd], hm1⟩

/-- con-leche: none — the expression-LIST layer. -/
theorem denoteEListGo_isSome {st : EStore} (hwf : StoreWF st) :
    ∀ (hs : List EIdx) {m : DMemo} {es : List Expr}, DMemoOK st m →
      denoteEList st hs = some es →
        ∃ m', denoteEListGo st m hs = some (m', es) ∧ DMemoOK st m' := by
  intro hs
  induction hs with
  | nil =>
    intro m es hm hd
    simp only [denoteEList, Option.some.injEq] at hd
    subst hd
    exact ⟨m, rfl, hm⟩
  | cons h hs ih =>
    intro m es hm hd
    rw [denoteEList] at hd
    cases h1 : denoteE st h with
    | none => rw [h1] at hd; simp at hd
    | some e =>
    cases h2 : denoteEList st hs with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    simp only [Option.some.injEq] at hd
    obtain ⟨m1, g1, hm1⟩ := denoteEGo_isSome' hwf hm h1
    obtain ⟨m2, g2, hm2⟩ := ih hm1 h2
    exact ⟨m2, by
      rw [denoteEListGo, g1]; simp only []; rw [g2]; simp only []; rw [hd], hm2⟩

/-- con-leche: none — the firing-mode layer. -/
theorem denoteFireGo_isSome {st : EStore} (hwf : StoreWF st) {m : DMemo}
    (hm : DMemoOK st m) {fr : IRecRuleFire} {f : RecRuleFire}
    (hd : denoteFire st fr = some f) :
    ∃ m', denoteFireGo st m fr = some (m', f) ∧ DMemoOK st m' := by
  cases fr with
  | inert =>
    simp only [denoteFire, Option.some.injEq] at hd; subst hd
    exact ⟨m, rfl, hm⟩
  | plain =>
    simp only [denoteFire, Option.some.injEq] at hd; subst hd
    exact ⟨m, rfl, hm⟩
  | nested lvls pins =>
    rw [denoteFire] at hd
    cases hl : denoteLList st.ls lvls with
    | none => rw [hl] at hd; simp at hd
    | some ls =>
    cases hp : denoteEList st pins with
    | none => rw [hl, hp] at hd; simp at hd
    | some ps =>
    rw [hl, hp] at hd
    simp only [Option.some.injEq] at hd
    obtain ⟨m1, g1, hm1⟩ := denoteEListGo_isSome hwf pins hm hp
    exact ⟨m1, by rw [denoteFireGo, hl, g1]; simp only []; rw [hd], hm1⟩

/-- con-leche: none — one rule. -/
theorem denoteRuleGo_isSome {st : EStore} (hwf : StoreWF st) {m : DMemo}
    (hm : DMemoOK st m) {rl : IRecRule} {r : RecRule}
    (hd : denoteRule st rl = some r) :
    ∃ m', denoteRuleGo st m rl = some (m', r) ∧ DMemoOK st m' := by
  rw [denoteRule] at hd
  cases hc : denoteN st.ns rl.ctor with
  | none => rw [hc] at hd; simp at hd
  | some c =>
  cases hf : denoteFire st rl.fire with
  | none => rw [hc, hf] at hd; simp at hd
  | some f =>
  cases hr : denoteE st rl.rhs with
  | none => rw [hc, hf, hr] at hd; simp at hd
  | some rhs =>
  rw [hc, hf, hr] at hd
  simp only [Option.some.injEq] at hd
  obtain ⟨m1, g1, hm1⟩ := denoteFireGo_isSome hwf hm hf
  obtain ⟨m2, g2, hm2⟩ := denoteEGo_isSome' hwf hm1 hr
  exact ⟨m2, by
    rw [denoteRuleGo, hc, g1]; simp only []; rw [g2]; simp only []; rw [hd], hm2⟩

/-- con-leche: none — a rule list. -/
theorem denoteRulesGo_isSome {st : EStore} (hwf : StoreWF st) :
    ∀ (rs : List IRecRule) {m : DMemo} {xs : List RecRule}, DMemoOK st m →
      denoteRules st rs = some xs →
        ∃ m', denoteRulesGo st m rs = some (m', xs) ∧ DMemoOK st m' := by
  intro rs
  induction rs with
  | nil =>
    intro m xs hm hd
    simp only [denoteRules, Option.some.injEq] at hd; subst hd
    exact ⟨m, rfl, hm⟩
  | cons r rs ih =>
    intro m xs hm hd
    rw [denoteRules] at hd
    cases h1 : denoteRule st r with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : denoteRules st rs with
    | none => rw [h1, h2] at hd; simp at hd
    | some ys =>
    rw [h1, h2] at hd
    simp only [Option.some.injEq] at hd
    obtain ⟨m1, g1, hm1⟩ := denoteRuleGo_isSome hwf hm h1
    obtain ⟨m2, g2, hm2⟩ := ih hm1 h2
    exact ⟨m2, by
      rw [denoteRulesGo, g1]; simp only []; rw [g2]; simp only []; rw [hd], hm2⟩

/-- con-leche: none — one type former of a parsed block, from the relation. -/
theorem denoteMTypeGo_of_rel {st : EStore} (hwf : StoreWF st) {m : DMemo}
    (hm : DMemoOK st m) {t : MIndTypeRec}
    {tc : ConLeche.Frontend.InModel.IndTypeRec} (h : MIndTypeRecRel st t tc) :
    ∃ m', denoteMTypeGo st m t = some (m', tc) ∧ DMemoOK st m' := by
  obtain ⟨m1, g1, hm1⟩ := denoteCVGo_isSome hwf hm h.cv
  refine ⟨m1, ?_, hm1⟩
  rw [denoteMTypeGo, g1, h.ctors]
  simp only []
  rw [h.nP, h.nIdx, h.isRec, h.isReflexive, h.numNested]

/-- con-leche: none — the type-former list. -/
theorem denoteMTypesGo_of_rel {st : EStore} (hwf : StoreWF st) :
    ∀ {ts : List MIndTypeRec} {tcs : List ConLeche.Frontend.InModel.IndTypeRec}
      {m : DMemo}, DMemoOK st m → ListRel (MIndTypeRecRel st) ts tcs →
      ∃ m', denoteMTypesGo st m ts = some (m', tcs) ∧ DMemoOK st m' := by
  intro ts tcs m hm h
  induction h generalizing m with
  | nil => exact ⟨m, rfl, hm⟩
  | @cons a b as bs hab _ ih =>
    obtain ⟨m1, g1, hm1⟩ := denoteMTypeGo_of_rel hwf hm hab
    obtain ⟨m2, g2, hm2⟩ := ih hm1
    exact ⟨m2, by rw [denoteMTypesGo, g1]; simp only []; rw [g2], hm2⟩

/-- con-leche: none — one constructor record. -/
theorem denoteMCtorGo_of_rel {st : EStore} (hwf : StoreWF st) {m : DMemo}
    (hm : DMemoOK st m) {c : MIndCtorRec}
    {cc : ConLeche.Frontend.InModel.IndCtorRec} (h : MIndCtorRecRel st c cc) :
    ∃ m', denoteMCtorGo st m c = some (m', cc) ∧ DMemoOK st m' := by
  obtain ⟨m1, g1, hm1⟩ := denoteCVGo_isSome hwf hm h.cv
  refine ⟨m1, ?_, hm1⟩
  rw [denoteMCtorGo, g1]
  simp only []
  rw [h.nP, h.nF]

/-- con-leche: none — the constructor list. -/
theorem denoteMCtorsGo_of_rel {st : EStore} (hwf : StoreWF st) :
    ∀ {cs : List MIndCtorRec} {ccs : List ConLeche.Frontend.InModel.IndCtorRec}
      {m : DMemo}, DMemoOK st m → ListRel (MIndCtorRecRel st) cs ccs →
      ∃ m', denoteMCtorsGo st m cs = some (m', ccs) ∧ DMemoOK st m' := by
  intro cs ccs m hm h
  induction h generalizing m with
  | nil => exact ⟨m, rfl, hm⟩
  | @cons a b as bs hab _ ih =>
    obtain ⟨m1, g1, hm1⟩ := denoteMCtorGo_of_rel hwf hm hab
    obtain ⟨m2, g2, hm2⟩ := ih hm1
    exact ⟨m2, by rw [denoteMCtorsGo, g1]; simp only []; rw [g2], hm2⟩

/-- con-leche: none — one recursor record. -/
theorem denoteMRecGo_of_rel {st : EStore} (hwf : StoreWF st) {m : DMemo}
    (hm : DMemoOK st m) {r : MIndRecRec}
    {rc : ConLeche.Frontend.InModel.IndRecRec} (h : MIndRecRecRel st r rc) :
    ∃ m', denoteMRecGo st m r = some (m', rc) ∧ DMemoOK st m' := by
  obtain ⟨m1, g1, hm1⟩ := denoteCVGo_isSome hwf hm h.cv
  obtain ⟨m2, g2, hm2⟩ := denoteRulesGo_isSome hwf r.rules hm1 h.rules
  refine ⟨m2, ?_, hm2⟩
  rw [denoteMRecGo, g1]
  simp only []
  rw [g2]
  simp only []
  rw [h.nP, h.nM, h.nm, h.nI]

/-- con-leche: none — the recursor list. -/
theorem denoteMRecsGo_of_rel {st : EStore} (hwf : StoreWF st) :
    ∀ {rs : List MIndRecRec} {rcs : List ConLeche.Frontend.InModel.IndRecRec}
      {m : DMemo}, DMemoOK st m → ListRel (MIndRecRecRel st) rs rcs →
      ∃ m', denoteMRecsGo st m rs = some (m', rcs) ∧ DMemoOK st m' := by
  intro rs rcs m hm h
  induction h generalizing m with
  | nil => exact ⟨m, rfl, hm⟩
  | @cons a b as bs hab _ ih =>
    obtain ⟨m1, g1, hm1⟩ := denoteMRecGo_of_rel hwf hm hab
    obtain ⟨m2, g2, hm2⟩ := ih hm1
    exact ⟨m2, by rw [denoteMRecsGo, g1]; simp only []; rw [g2], hm2⟩

/-- con-leche: none — the block the seam reads back is the block the relation
names: `denoteCVGo`'s existence direction through the three member families,
then `BlockRecRel`'s three `ListRel` clauses. -/
theorem denoteBlockRec_eq_of_rel {st : EStore} (hwf : StoreWF st) {b : BlockRec}
    {bP : ConLeche.Frontend.InModel.BlockRec} (h : BlockRecRel st b bP) :
    denoteBlockRec st b = some bP := by
  obtain ⟨m1, g1, hm1⟩ := denoteMTypesGo_of_rel hwf (DMemoOK.empty st) h.types
  obtain ⟨m2, g2, hm2⟩ := denoteMCtorsGo_of_rel hwf hm1 h.ctors
  obtain ⟨m3, g3, hm3⟩ := denoteMRecsGo_of_rel hwf hm2 h.recs
  rw [denoteBlockRec, denoteBlockRecGo, g1]
  simp only []
  rw [g2]
  simp only []
  rw [g3]

/-! ### `nameHandle?`, both directions

`ctxOf` probes the name store with `nameHandle?` where `CtxRel` quantifies over
handles that DENOTE, so the bridge between them is two lemmas: what the probe
answers denotes the name it was asked for, and a name that denotes at all is
one the probe answers.  The second needs `denoteN_inj` — two handles denoting
one name are one handle — which is DESIGN §8.3's soundness obligation. -/

/-- con-leche: none — a handle `nameHandle?` answers denotes the name it was
asked for. -/
theorem nameHandle?_sound {st : NStore} (hwf : NStoreWF st) :
    ∀ (n : ConLeche.Name) {h : NIdx}, nameHandle? st n = some h →
      denoteN st h = some n := by
  obtain ⟨rk, hw⟩ := hwf
  intro n
  induction n with
  | anonymous =>
    intro h hf
    rw [nameHandle?] at hf
    have hv := Arena.NStore.view_of_find ⟨rk, hw⟩ hf
    rw [Arena.denoteN_unfold hw hv]; rfl
  | str p s ih =>
    intro h hf
    rw [nameHandle?] at hf
    cases hp : nameHandle? st p with
    | none => rw [hp] at hf; exact absurd hf (by simp)
    | some hpi =>
      rw [hp] at hf
      have hdp := ih hp
      have hv := Arena.NStore.view_of_find ⟨rk, hw⟩ hf
      rw [Arena.denoteN_unfold hw hv]
      simp [Arena.denoteNView, hdp]
  | num p k ih =>
    intro h hf
    rw [nameHandle?] at hf
    cases hp : nameHandle? st p with
    | none => rw [hp] at hf; exact absurd hf (by simp)
    | some hpi =>
      rw [hp] at hf
      have hdp := ih hp
      have hv := Arena.NStore.view_of_find ⟨rk, hw⟩ hf
      rw [Arena.denoteN_unfold hw hv]
      simp [Arena.denoteNView, hdp]

/-- con-leche: none — a node the store holds is a node `NStore.find?`
answers. -/
theorem find?_isSome_of_view {st : NStore} {rk : NIdx → Nat} (hw : Arena.NWFAt st rk)
    {h : NIdx} {v : NNodeView} (hv : st.view h = some v) :
    (st.find? v).isSome = true := by
  simp only [Arena.NStore.find?]
  cases hp : st.pers.find? v with
  | some i => simp
  | none =>
    by_cases hper : h.isPersistent = true
    · rw [(hw.consP v h).mpr ⟨hv, hper⟩] at hp; exact absurd hp (by simp)
    · have hper' : h.isPersistent = false := by simpa using hper
      have hon : st.scratchOn = true := by
        by_cases hoff : st.scratchOn = true
        · exact hoff
        · exfalso
          have hoff' : st.scratchOn = false := by simpa using hoff
          rw [Arena.NStore.view, if_neg hper, if_neg (by rw [hoff']; simp)] at hv
          exact absurd hv (by simp)
      rw [if_pos hon, (hw.consS v h).mpr ⟨hv, hper'⟩]
      simp

/-- con-leche: none — a name that denotes is a name `nameHandle?` answers. -/
theorem nameHandle?_isSome {st : NStore} (hwf : NStoreWF st) :
    ∀ (n : ConLeche.Name) {h : NIdx}, denoteN st h = some n →
      (nameHandle? st n).isSome = true := by
  obtain ⟨rk, hw⟩ := hwf
  intro n
  induction n with
  | anonymous =>
    intro h hd
    obtain ⟨v, hv⟩ := Arena.denoteN_view hd
    rw [Arena.denoteN_unfold hw hv] at hd
    obtain rfl := Arena.denoteNView_anonymous hd
    rw [nameHandle?]
    exact find?_isSome_of_view hw hv
  | str p s ih =>
    intro h hd
    obtain ⟨v, hv⟩ := Arena.denoteN_view hd
    rw [Arena.denoteN_unfold hw hv] at hd
    obtain ⟨pi, rfl, hdp⟩ := Arena.denoteNView_str hd
    have hsi := ih hdp
    cases hpq : nameHandle? st p with
    | none => rw [hpq] at hsi; exact absurd hsi (by simp)
    | some hpi =>
      obtain rfl : hpi = pi :=
        Arena.denoteN_inj ⟨rk, hw⟩ (nameHandle?_sound ⟨rk, hw⟩ p hpq) hdp
      rw [nameHandle?, hpq]
      exact find?_isSome_of_view hw hv
  | num p k ih =>
    intro h hd
    obtain ⟨v, hv⟩ := Arena.denoteN_view hd
    rw [Arena.denoteN_unfold hw hv] at hd
    obtain ⟨pi, rfl, hdp⟩ := Arena.denoteNView_num hd
    have hsi := ih hdp
    cases hpq : nameHandle? st p with
    | none => rw [hpq] at hsi; exact absurd hsi (by simp)
    | some hpi =>
      obtain rfl : hpi = pi :=
        Arena.denoteN_inj ⟨rk, hw⟩ (nameHandle?_sound ⟨rk, hw⟩ p hpq) hdp
      rw [nameHandle?, hpq]
      exact find?_isSome_of_view hw hv

/-- con-leche: ConLeche/Frontend/InModel/Mutual.lean:119-124 Ctx — the context
the seam builds IS the context the relation names.  Function extensionality at
three fields, each of which probes the name store with `nameHandle?` where the
relation quantifies over handles that denote — and the two meet because
`denoteN` is injective (DESIGN §8.3's soundness obligation).

`nameHandle?`'s own exactness — both halves — plus `denoteN_inj`, then
`denoteEShared_eq_denoteE` at the `tbl` field and `denoteBlockRec_eq_of_rel`
at the `blocks` one.  **The three COVER clauses of `CtxRel` are what make this
true at all** (round 2's finding 12): a name the store never interned has no
handle, `ctxOf` answers `none` / `0` there, and nothing but a cover clause
says con-leche's context does too. -/
theorem ctxOf_eq_of_rel {st : EStore} (hwf : StoreWF st) {c : Ctx}
    {cc : ConLeche.Frontend.InModel.Ctx} (h : CtxRel st c cc) :
    ctxOf st c = cc := by
  have hns : NStoreWF st.ns := by
    obtain ⟨rk, hw⟩ := hwf
    obtain ⟨rkl, hl⟩ := hw.lss.ls
    exact hl.ns
  cases cc with
  | mk tbl heights blocks =>
  simp only [ctxOf]
  congr 1
  · funext n
    cases hnh : nameHandle? st.ns n with
    | none =>
      cases htn : tbl n with
      | none => rfl
      | some q =>
        obtain ⟨hh, hdh⟩ := h.tblCover n q htn
        have hs := nameHandle?_isSome hns n hdh
        rw [hnh] at hs; exact absurd hs (by simp)
    | some hh =>
      simp only []
      have hdh : denoteN st.ns hh = some n := nameHandle?_sound hns n hnh
      have hrel := h.tbl hh n hdh
      simp only [] at hrel
      cases hc : c.tbl hh with
      | none => exact (hrel.none_left hc).symm
      | some p =>
        obtain ⟨q, hq, hpq⟩ := hrel.some_left hc
        rw [hq]
        simp only [hpq.1, denoteEShared_eq_denoteE hwf p.2, hpq.2]
  · funext n
    cases hnh : nameHandle? st.ns n with
    | none =>
      by_cases hz : heights n = 0
      · rw [hz]
      · obtain ⟨hh, hdh⟩ := h.heightsCover n hz
        have hs := nameHandle?_isSome hns n hdh
        rw [hnh] at hs; exact absurd hs (by simp)
    | some hh =>
      simp only []
      exact h.heights hh n (nameHandle?_sound hns n hnh)
  · funext n
    cases hnh : nameHandle? st.ns n with
    | none =>
      cases htn : blocks n with
      | none => rfl
      | some b =>
        obtain ⟨hh, hdh⟩ := h.blocksCover n b htn
        have hs := nameHandle?_isSome hns n hdh
        rw [hnh] at hs; exact absurd hs (by simp)
    | some hh =>
      simp only []
      have hdh : denoteN st.ns hh = some n := nameHandle?_sound hns n hnh
      have hrel := h.blocks hh n hdh
      simp only [] at hrel
      cases hc : c.blocks hh with
      | none => exact (hrel.none_left hc).symm
      | some bb =>
        obtain ⟨bP, hbP, hbrel⟩ := hrel.some_left hc
        rw [hbP]
        exact denoteBlockRec_eq_of_rel hwf hbrel

end ConRon.Bridge.Frontend
