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

So the module introduces **`StoreWFP`** — `StoreWF` minus the two freshness
clauses — with three facts about it:

| | |
|---|---|
| `StoreWFP.of_wf` | a well-formed store is promotion-well-formed (forget two clauses) |
| `EStore.internPersistent_spec` | each promote-intern preserves `StoreWFP`, extends, and decodes to the view |
| `StoreWFP.dropScratch_wf` | **the bracket closes**: emptying the scratch tier restores `fresh` vacuously, so `StoreWFP` becomes `StoreWF` again |

`StoreWFP` is a *strictly weaker* invariant than `StoreWF`, so nothing above
it weakens: a theorem that concludes `StoreWF` still concludes `StoreWF`,
and `StoreWFP` appears only between an `enterScratch` and the `dropScratch`
that closes the same bracket.

**What is `sorry` here and why** (task #97-P3-Checker, the sorry list): the
four `internPersistent_spec`s and `dropScratch_wf` are the arena's *store*
layer, not the bridge's — they are `Arena/WFProofs.lean`'s `intern_wf` /
`wf_of_scr_empty` arguments at a second entry point, and `WFProofs.lean` is
7 658 lines of exactly that argument for `intern`.  Re-running it for
`internPersistent` is a store-layer task (it belongs beside `intern_wf`, not
here), and it is the largest single item this tier owes.  Everything above
this file consumes the statements and nothing else, so discharging them is a
drop-in.
-/
import ConRon.Bridge.Promote.Pers

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## `StoreWF` minus the freshness clauses

Clause for clause `Arena/WF.lean`'s `EWFAt`, with `fresh` and `bmFresh`
dropped and nothing else changed. -/

/-- con-leche: none — arena infrastructure; the expression store's
well-formedness MINUS the two cross-tier freshness clauses, at an explicit
rank.  `Arena/WF.lean`'s `EWFAt` without `fresh` and `bmFresh`; the two
nested stores keep their own full invariants, because `internPersistent`
at an expression node never appends to them (the name, level and level-list
promotions have their own entries below, each with the same weakening at its
own level). -/
structure EWFAtP (st : EStore) (rk : EIdx → Nat) : Prop where
  lss : LsStoreWF st.lss
  childOK : ∀ i v, st.view i = some v → ∀ c ∈ v.echildren,
    (st.view c).isSome = true ∧ rk c < rk i ∧
      (i.isPersistent = true → c.isPersistent = true)
  nchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.nchildren,
    (st.ns.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  lchildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lchildren,
    (st.ls.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  lschildOK : ∀ i v, st.view i = some v → ∀ c ∈ v.lschildren,
    (st.lss.view c).isSome = true ∧ (i.isPersistent = true → c.isPersistent = true)
  rankP : ∀ i, i.isPersistent = true → (st.view i).isSome = true →
    rk i < st.persCount
  rankS : ∀ i, i.isPersistent = false → (st.view i).isSome = true →
    rk i < st.nodeCount
  bmChildOK : ∀ i ty b mi, st.viewBindI i = some (ty, b, mi) →
    (st.viewBM mi).isSome = true ∧ (i.isPersistent = true → mi.isPersistent = true)
      ∧ mi.tag = 0
  consP : ∀ v i, st.persFind? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = true)
  consS : ∀ v i, st.scrFind? v = some i ↔
    (st.view i = some v ∧ i.isPersistent = false)
  bmConsP : ∀ m i, st.pers.findBM m = some i ↔
    (st.viewBM i = some m ∧ i.isPersistent = true ∧ i.tag = 0)
  bmConsS : ∀ m i, st.scr.findBM m = some i ↔
    (st.viewBM i = some m ∧ i.isPersistent = false ∧ i.tag = 0)
  bmKeyP : ∀ v mj i, st.pers.find? v mj = some i →
    v.bmOf = none ∨ ∃ m, st.pers.findBM m = some mj
  bmKeyS : ∀ v mj i, st.scr.find? v mj = some i →
    v.bmOf = none ∨ ∃ m, st.findBM m = some mj
  derExact : ∀ i v, st.view i = some v → st.derived i = st.derOfView v
  bmDerExact : ∀ i m, st.viewBM i = some m → st.bmDer i = (hash m.pw, m.pw.hasParams)
  sizedP : st.pers.Sized
  sizedS : st.scr.Sized
  capP : ∀ v, st.pers.sizeOf v ≤ Idx.idxCap
  capS : ∀ v, st.scr.sizeOf v ≤ Idx.idxCap
  bmCapP : st.pers.bmSize ≤ Idx.idxCap
  bmCapS : st.scr.bmSize ≤ Idx.idxCap
  scrOff : st.scratchOn = false → st.scr = ETables.empty
  sync : st.scratchOn = st.lss.scratchOn

/-- con-leche: none — arena infrastructure; **the promotion-time store
invariant**: `StoreWF` while a promotion is in flight. -/
def StoreWFP (st : EStore) : Prop := ∃ rk, EWFAtP st rk

/-- con-leche: none — arena infrastructure; a well-formed store is
promotion-well-formed.  Two clauses forgotten, nothing else. -/
theorem StoreWFP.of_wf {st : EStore} (h : StoreWF st) : StoreWFP st := by
  obtain ⟨rk, h⟩ := h
  refine ⟨rk, ?_⟩
  exact {
    lss := h.lss
    childOK := h.childOK
    nchildOK := h.nchildOK
    lchildOK := h.lchildOK
    lschildOK := h.lschildOK
    rankP := h.rankP
    rankS := h.rankS
    bmChildOK := h.bmChildOK
    consP := h.consP
    consS := h.consS
    bmConsP := h.bmConsP
    bmConsS := h.bmConsS
    bmKeyP := h.bmKeyP
    bmKeyS := h.bmKeyS
    derExact := h.derExact
    bmDerExact := h.bmDerExact
    sizedP := h.sizedP
    sizedS := h.sizedS
    capP := h.capP
    capS := h.capS
    bmCapP := h.bmCapP
    bmCapS := h.bmCapS
    scrOff := h.scrOff
    sync := h.sync }

/-! ## The bracket closes

`dropScratch` replaces the scratch tier by `ETables.empty`, so `scrFind?` is
constantly `none` afterwards and `fresh`/`bmFresh` hold vacuously — which is
the whole content of "the promotion's transient exception is not observable".
Every other clause is `Arena/WFProofs.lean`'s `wf_of_scr_empty`, whose
argument never reads `fresh` of its input. -/

/-- con-leche: none — arena infrastructure; **the promotion bracket's closing
step**: dropping the scratch tier turns the promotion-time invariant back into
the store invariant.

`sorry`: `Arena/WFProofs.lean`'s `EStore.wf_of_scr_empty` proves exactly this
from `EWFAt`; re-running it from `EWFAtP` is a mechanical weakening of that
proof (it establishes the output's `fresh`/`bmFresh` vacuously from
`scr = empty` and never uses the input's), and it belongs in `WFProofs.lean`
beside the original.  Task #97-P3-Checker's sorry list, item 1. -/
theorem StoreWFP.dropScratch_wf {st : EStore} (h : StoreWFP st) :
    StoreWF st.dropScratch := by
  sorry

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

/-- con-leche: none — arena infrastructure; `NStore.internPersistent`'s spec:
`NStore.intern_spec` with the persistent branch forced.

`sorry`: `Arena/WFProofs.lean`'s `NStore.intern_wf` / `intern_ext` /
`intern_view_spec` at the same branch.  Task #97-P3-Checker's sorry list,
item 2. -/
theorem NStore.internPersistent_spec {st : NStore} {w : NNodeView}
    (h : NStoreWF st) (hv : st.ViewOK w) (hp : NNodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    NStoreWF (st.internPersistent w).1 ∧ NExt st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersN (st.internPersistent w).2 := by
  sorry

/-- con-leche: none — arena infrastructure; `LStore.internPersistent`'s spec.

`sorry`: as `NStore.internPersistent_spec`.  Task #97-P3-Checker's sorry
list, item 2. -/
theorem LStore.internPersistent_spec {st : LStore} {w : LNodeView}
    (h : LStoreWF st) (hv : st.ViewOK w) (hp : LNodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    LStoreWF (st.internPersistent w).1 ∧ LExt st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersL (st.internPersistent w).2 := by
  sorry

/-- con-leche: none — arena infrastructure; `LsStore.internPersistent`'s spec.

`sorry`: as `NStore.internPersistent_spec`.  Task #97-P3-Checker's sorry
list, item 2. -/
theorem LsStore.internPersistent_spec {st : LsStore} {w : LsNodeView}
    (h : LsStoreWF st) (hv : st.ViewOK w) (hp : LsNodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    LsStoreWF (st.internPersistent w).1 ∧ LsExt st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersLs (st.internPersistent w).2 := by
  sorry

/-- con-leche: none — arena infrastructure; **`EStore.internPersistent`'s
spec**, at the WEAKENED invariant — this is the one statement `fresh` forces
out of `StoreWF` and into `StoreWFP` (the module note quotes the reason).

`sorry`: `Arena/WFProofs.lean`'s `EStore.intern_wf` / `intern_ext` /
`intern_view_spec` at the persistent branch, with `fresh`/`bmFresh` dropped
from both sides.  Task #97-P3-Checker's sorry list, item 2. -/
theorem EStore.internPersistent_spec {st : EStore} {w : ENodeView}
    (h : StoreWFP st) (hv : st.ViewOK w) (hp : ENodeView.Pers w)
    (hcap : st.capOKPersistent w) :
    StoreWFP (st.internPersistent w).1 ∧ Ext st (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      PersE (st.internPersistent w).2 ∧
      (st.internPersistent w).1.scratchOn = st.scratchOn := by
  sorry

end ConRon.Bridge
