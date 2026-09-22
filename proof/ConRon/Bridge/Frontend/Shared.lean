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

/-- con-leche: none — **the intern is the readback's inverse**: what
`internExpr` returns denotes what it was given, in the store the call leaves
behind, and it is persistent when the scratch tier is closed.

`sorry`: the structural recursion over `ConLeche.Expr`, each arm one
`Bridge/Specs.lean` `internE` face, with `EMemoOK` carried and
`Bridge/Rel.lean`'s `denote_ext` moving the earlier children forward.  The
persistence clause is FREE now (`Bridge/Frontend/Rel.lean`'s `PersE_of_view`
at the spec's `view` conjunct, round 2's replacement for finding 9.1).

**What is missing is two specs, and they are not in this tier's files**
(round 2's finding 13): `internExprGo`'s `.sort` arm calls `internLevel` and
its `.const` arm calls `internLevels`, and `Bridge/Specs.lean` states
`internLNode_spec` / `internLsNode_spec` (the NODE interns) but no
`internLevel_spec` / `internLevels_spec` for a whole transient `Level` tree or
`List Level` — where it does state `internName_spec` for a whole `Name`.  The
two are `internName_spec`'s proof verbatim, one structural induction each, and
they belong beside it.  Task #97-P3-Frontend's sorry list, item 2. -/
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
by list — eleven more layers, each of them three lines once the leaf is in
hand (`internNameList`, `internLevelList`, `internExprList`, `internCV`,
`internFire`, `internRule`, `internRules`, `internCaps`, `internProjTable`,
`internCI`, `internCIList`, `internDecl`).  **This is the last blocker of item
8** (`inProcessModeller_wf` / `_refines`): items 1 and 3 closed in round 2, so
the seam's two promises now wait on the intern direction alone.  Task
#97-P3-Frontend's sorry list, item 2. -/
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
