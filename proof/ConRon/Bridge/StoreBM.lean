/-
# `ConRon.Bridge.StoreBM` — the binder-datum store's monotonicity

The third store obligation this phase found, and the one that is still open at
its ONE consumer: `Bridge/ExprOps/Inst1.lean`'s binder arm.

**What the walk does.**  A rebuilding walk takes a binder apart with
`viewBindI` (getting the datum as a HANDLE, task #97-P6-16), recurses into the
two children — which INTERN, so the store grows — and puts the binder back
with `internBindIE tg t b' mi`, whose precondition (`Bridge/Specs.lean`'s
`internBindIE_spec'`) is `(st.viewBM mi).isSome` at the store the recursion
left behind.  `Bridge/Rel.lean`'s `bmOK_of_viewBindI` answers it at the store
the `viewBindI` read was taken in.  The gap is exactly one fact:

> interning a node leaves the binder-datum store's decoding alone at every
> datum handle that already decoded.

`Ext` does not say it — `Ext` is about `denoteE`/`denoteL`/`denoteN`/`denoteLs`
and a `BMIdx` denotes nothing — so it has to be said separately.  It is TRUE
and cheap: `intern` is `internBMOfView` followed by `internAt`, the first
appends to `bms` (which only grows, `ETables.getBM_pushBM_mono`) and the
second does not touch it at all (`ETables.getBM_push`).  The four lemmas below
are `Arena/WFProofs.lean`'s own `view_intern_mono` argument played at `getBM`
instead of at `get`.

**What is left to do with them** (the next round's first item): add the
conjunct

    ∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m

to `internE_spec`'s postcondition, to the ten per-constructor faces that
derive from it, to `internBindIE_spec'`, and to each walk's `…Spec` record —
a mechanical postcondition change across twelve specs.  Then
`Inst1.lean`'s two open binder goals close by `arm_hyp`.
-/
import ConRon.Bridge.Rel

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — appending a
binder DATUM leaves every datum that already decoded decoding the same.  The
datum store only grows, and `ETables.getBM_pushBM_mono` is that. -/
theorem EStore.viewBM_internBM_mono (st : EStore) (m : ConLeche.BinderMeta)
    {i : BMIdx} {mm : ConLeche.BinderMeta} (h : st.viewBM i = some mm) :
    (st.internBM m).1.viewBM i = some mm := by
  rcases EStore.internBM_cases st m with he | he | he <;> rw [he]
  · exact h
  all_goals
    refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ h <;>
      first
      | rfl
      | exact fun _ _ hk => by
          first | exact hk | exact ETables.getBM_pushBM_mono hk

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the same at
`intern`'s datum half, which is `internBM` at a binder view and the identity
at every other. -/
theorem EStore.viewBM_internBMOfView_mono (st : EStore) (w : ENodeView)
    {i : BMIdx} {mm : ConLeche.BinderMeta} (h : st.viewBM i = some mm) :
    (st.internBMOfView w).1.viewBM i = some mm := by
  cases w
  case lam _ _ m => exact EStore.viewBM_internBM_mono st m h
  case forallE _ _ m => exact EStore.viewBM_internBM_mono st m h
  all_goals exact h

/-- con-leche: none — arena infrastructure; `intern`'s NODE half does not
touch the datum store at all (`ETables.getBM_push`). -/
theorem EStore.viewBM_internAt_mono (st : EStore) (w : ENodeView) (mi : BMIdx)
    {i : BMIdx} {mm : ConLeche.BinderMeta} (h : st.viewBM i = some mm) :
    (st.internAt w mi).1.viewBM i = some mm := by
  rcases EStore.internAt_cases st w mi with he | he | he <;> rw [he]
  · exact h
  all_goals
    refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ h <;>
      first
      | rfl
      | exact fun _ _ hk => by
          first | exact hk | (rw [ETables.getBM_push]; exact hk)

/-- con-leche: none — **the fact the binder arm needs**: interning a node
leaves every binder datum that already decoded decoding the same. -/
theorem EStore.viewBM_intern_mono (st : EStore) (w : ENodeView) {i : BMIdx}
    {mm : ConLeche.BinderMeta} (h : st.viewBM i = some mm) :
    (st.intern w).1.viewBM i = some mm := by
  simp only [EStore.intern]
  exact EStore.viewBM_internAt_mono _ w _
    (EStore.viewBM_internBMOfView_mono st w h)

#print axioms EStore.viewBM_intern_mono

end ConRon.Bridge
