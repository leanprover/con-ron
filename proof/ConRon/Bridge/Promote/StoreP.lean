/-
# `ConRon.Bridge.Promote.StoreP` — the `internPersistent` obligation, stated for the BRACKET

`Arena/Store.lean`'s section note "Interning into the PERSISTENT tier while
the scratch tier is on" (lines 1754-1800) states the obligation this module
owes, and it states it for the BRACKET rather than for the operation.  Quoted,
because the shape of the whole module follows from it:

> * `internPersistent` preserves every clause of `StoreWF` by the persistent
>   branch of `intern`'s own argument — it IS that branch — with ONE added
>   precondition and ONE transient exception.
> * **Added precondition**: `childOK` carries `i.isPersistent → c.isPersistent`,
>   so the view handed to `internPersistent` must have PERSISTENT CHILDREN.
> * **Transient exception — `fresh`**: […] a node BUILT in the scratch tier out
>   of already-persistent children sits in the scratch table under a view whose
>   children are persistent, and promoting it appends that same view to the
>   persistent table.  So `fresh` is broken while the promotion runs.  It is not
>   observable […] and `dropScratch` empties the scratch tier, which restores
>   `fresh` vacuously.  The obligation P3 owes is therefore stated for the
>   BRACKET: `StoreWF` minus `fresh` is preserved by each `internPersistent`,
>   and `promote … dropScratch` as a whole takes `StoreWF` to `StoreWF`.

**The invariant is `Arena/WF.lean`'s `StoreWF'`** (task #97-P3-Promote).  This
module used to define its own `EWFAtP`/`StoreWFP` — `StoreWF` minus `fresh`
and `bmFresh`, nesting the STRONG `LsStoreWF` and keeping `consS` as an `↔` —
and task #97-P5-Fresh §6 found three things wrong with it: the nested
invariant must be the weak one too (the name, level and level-list promotions
append to those tiers and break THEIR `fresh`), `consS`'s `←` half does not
survive promoting a binder datum (`EStore.internBMPersistent_breaks_consS`),
and the three nested `internPersistent_spec`s concluded the FULL invariant,
which finding 17's `internPersistent_breaks_fresh` refutes.  `StoreWF'` is the
same idea stated right, one tier down where the store layer proves it, with
the bracket's closing step (`StoreWF'.dropScratch_wf`) already proved; so
`EWFAtP`/`StoreWFP` are deleted and the two names are one notion in one place.

| | |
|---|---|
| `StoreWF'.of_wf` (`Arena/WFProofs.lean`) | a well-formed store is promotion-well-formed |
| `EStore.internPersistent_spec` (here) | each promote-intern preserves `StoreWF'`, extends, and decodes to the view |
| `StoreWF'.dropScratch_wf` (`Arena/WFProofs.lean`) | **the bracket closes**: emptying the scratch tier restores the freshness clauses vacuously |

All four `internPersistent_spec`s below are PROVED — each is the store
layer's `…internPersistent_wf'` / `_ext` / `_view` / `_pers` assembled, which
tasks #97-P5-Fresh and #97-P5-Specs round 3 put in `Arena/WFProofs.lean`.
-/
import ConRon.Bridge.Promote.Weak

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The four promote-interns

Each is `intern`'s persistent branch with the `scratchOn = false` side
condition replaced by the view's own persistence, so each has `intern_spec`'s
three conjuncts: the invariant survives, every handle keeps its denotation,
and the answer decodes to the view that was interned. -/

/-- con-leche: none — arena infrastructure; a name view's children are
persistent. -/
def NNodeView.Pers (v : NNodeView) : Prop := ∀ c ∈ v.children, PersN c

/-- con-leche: none — arena infrastructure; a level view's children are
persistent. -/
structure LNodeView.Pers (v : LNodeView) : Prop where
  lvl : ∀ c ∈ v.lchildren, PersL c
  nm : ∀ c ∈ v.nchildren, PersN c

/-- con-leche: none — arena infrastructure; a level-list view's children are
persistent. -/
def LsNodeView.Pers (v : LsNodeView) : Prop := ∀ c ∈ v, PersL c

/-- con-leche: none — arena infrastructure; an expression view's children are
persistent, at all four handle kinds. -/
structure ENodeView.Pers (v : ENodeView) : Prop where
  expr : ∀ c ∈ v.echildren, PersE c
  nm : ∀ c ∈ v.nchildren, PersN c
  lvl : ∀ c ∈ v.lchildren, PersL c
  lst : ∀ c ∈ v.lschildren, PersLs c

/-- con-leche: none — arena infrastructure; the two spellings of "the view's
children are persistent" agree: this module's `ENodeView.Pers` (stated with
`Pers…`) and `Arena/WF.lean`'s `EViewPers` (stated with `isPersistent`). -/
theorem ENodeView.Pers.toViewPers {v : ENodeView} (hp : ENodeView.Pers v) :
    EViewPers v := ⟨hp.expr, hp.nm, hp.lvl, hp.lst⟩

theorem LNodeView.Pers.toViewPers {v : LNodeView} (hp : LNodeView.Pers v) :
    LViewPers v := ⟨hp.lvl, hp.nm⟩

/-- con-leche: none — arena infrastructure; `NStore.internPersistent`'s spec,
at the promote window's invariant: `NStore.intern_spec` with the persistent
branch forced.

**Statement repaired** (task #97-P3-Promote, authorised): it concluded the
FULL `NStoreWF`, which task #97-P5-Fresh's finding 17
(`NStore.internPersistent_breaks_fresh`) refutes at hypotheses this statement
allows; hypothesis and conclusion are now `NStoreWF'`.  PROVED from the store
layer's four lemmas. -/
theorem NStore.internPersistent_spec {st : NStore} {w : NNodeView}
    (h : NStoreWF' st) (hv : st.ViewOK w) (hp : NNodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    NStoreWF' (st.internPersistent w).1 ∧ NExt st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersN (st.internPersistent w).2 :=
  ⟨NStore.internPersistent_wf' h hv hp hcap, NStore.internPersistent_ext st w,
    NStore.internPersistent_view h (fun _ => hcap),
    NStore.internPersistent_pers h (fun _ => hcap)⟩

/-- con-leche: none — arena infrastructure; `LStore.internPersistent`'s spec,
at the promote window's invariant.  Repaired and PROVED as
`NStore.internPersistent_spec`. -/
theorem LStore.internPersistent_spec {st : LStore} {w : LNodeView}
    (h : LStoreWF' st) (hv : st.ViewOK w) (hp : LNodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    LStoreWF' (st.internPersistent w).1 ∧ LExt st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersL (st.internPersistent w).2 :=
  ⟨LStore.internPersistent_wf' h hv hp.toViewPers hcap, LStore.internPersistent_ext st w,
    LStore.internPersistent_view h (fun _ => hcap),
    LStore.internPersistent_pers h (fun _ => hcap)⟩

/-- con-leche: none — arena infrastructure; `LsStore.internPersistent`'s spec,
at the promote window's invariant.  Repaired and PROVED as
`NStore.internPersistent_spec`. -/
theorem LsStore.internPersistent_spec {st : LsStore} {w : LsNodeView}
    (h : LsStoreWF' st) (hv : st.ViewOK w) (hp : LsNodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    LsStoreWF' (st.internPersistent w).1 ∧ LsExt st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersLs (st.internPersistent w).2 :=
  ⟨LsStore.internPersistent_wf' h hv hp hcap, LsStore.internPersistent_ext st w,
    LsStore.internPersistent_view h (fun _ => hcap),
    LsStore.internPersistent_pers h (fun _ => hcap)⟩

/-- con-leche: none — arena infrastructure; **`EStore.internPersistent`'s
spec**, at the promote window's invariant `StoreWF'` (it was stated at
`StoreWFP`, whose `consS ↔` the datum half refutes — task #97-P5-Fresh §3).
PROVED: `EStore.internPersistent_spec'` (the store layer's, task #97-P5-Specs
round 3) plus `_ext` and `scratchOn_internPersistent`. -/
theorem EStore.internPersistent_spec {st : EStore} {w : ENodeView}
    (h : StoreWF' st) (hv : st.ViewOK w) (hp : ENodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    StoreWF' (st.internPersistent w).1 ∧ Ext st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersE (st.internPersistent w).2 ∧
      (st.internPersistent w).1.scratchOn = st.scratchOn := by
  obtain ⟨a, b, c⟩ := EStore.internPersistent_spec' h hv hp.toViewPers
    (EStore.persCapBM.of_needs hcap.2) (EStore.persCapNode.of_size hcap.1)
  exact ⟨a, EStore.internPersistent_ext st w, b, c,
    EStore.scratchOn_internPersistent st w⟩

end ConRon.Bridge
