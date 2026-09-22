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

/-- con-leche: none — **the memoised readback's step**: at a memo that records
only true denotations, `denoteEGo` answers `denoteE` and leaves the memo
recording only true denotations.

`sorry`: the ten-arm fuel induction, in `Bridge/ExprOps/Inst1.lean`'s shape —
each arm rebuilds the node from children the induction hypothesis has already
identified with `denoteE`'s, and the `insert` clause is
`Bridge/StateOK.lean`'s `MemoOK.insert`.  The fuel side condition is
`StoreWF`'s rank (`denoteE` is defined by the same recursion at
`st.nodeCount + 1`).  Task #97-P3-Frontend's sorry list, item 1. -/
theorem denoteEGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {fuel : Nat} {h : EIdx} {e : Expr}
    (hrun : denoteEGo st m fuel h = some (m', e)) :
    denoteE st h = some e ∧ DMemoOK st m' := by
  sorry

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

/-- con-leche: none — the memoised `ConstantVal` readback is
`Bridge/Rel.lean`'s `denoteCV`.

`sorry`: three reads and `denoteEGo_spec`.  Task #97-P3-Frontend's sorry list,
item 1. -/
theorem denoteCVGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {cv : IConstantVal} {c : ConstantVal}
    (hrun : denoteCVGo st m cv = some (m', c)) :
    denoteCV st cv = some c ∧ DMemoOK st m' := by
  sorry

/-- con-leche: none — the memoised block readback is `Bridge/Rel.lean`'s
`denoteCIList`.  This is the one `readCIList` (hence the modeller seam) runs.

`sorry`: seven arms over `denoteCVGo_spec` and the rule/table families.  Task
#97-P3-Frontend's sorry list, item 1. -/
theorem denoteCIListGo_spec {st : EStore} (hwf : StoreWF st) {m m' : DMemo}
    (hm : DMemoOK st m) {cs : List IConstantInfo} {csP : List ConstantInfo}
    (hrun : denoteCIListGo st m cs = some (m', csP)) :
    denoteCIList st cs = some csP ∧ DMemoOK st m' := by
  sorry

/-- con-leche: none — `readExpr`, the `AM` face: it never moves the store and
its answer is the denotation.

`sorry`: `denoteEShared_eq` plus the `AM` unfolding.  Task #97-P3-Frontend's
sorry list, item 1. -/
theorem readExpr_run {s s' : AState} (hok : StateOK s) {h : EIdx} {e : Expr}
    (hrun : readExpr h s = .ok (e, s')) :
    s' = s ∧ denoteE s.store h = some e := by
  sorry

/-- con-leche: none — `readCIList`, the `AM` face. -/
theorem readCIList_run {s s' : AState} (hok : StateOK s)
    {cs : List IConstantInfo} {csP : List ConstantInfo}
    (hrun : readCIList cs s = .ok (csP, s')) :
    s' = s ∧ denoteCIList s.store cs = some csP := by
  sorry

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
