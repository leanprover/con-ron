/-
# `ConRon.Bridge.Checker.Canon` — the pinned-block comparison

`Arena/Canon.lean` is the twin of `ConLeche/Kernel/Canon.lean`: alpha-and-
universe-renaming-insensitive comparison of a stream record against a pinned
one.  It is what recognises a `Nat` block, a quotient record and the
`Quot.sound` axiom, and it is the only comparison in the checker that is NOT
handle equality — a stream's universe parameter may be spelled differently
from the pin's, so the comparison canonicalises both sides against a generated
name list (`canonNames`).

**The bridge's shape is `RelV`'s** (`Bridge/Rel.lean`): the answer is a
`Bool`, which names no handle, so there is no target store and the tier's
cheapest shape applies — task #97-P3-0 §5's finding 1, *"the cheapest group is
the one with no target store"*.

**The one subtlety is the generated names.**  `canonNames n` interns `n` fresh
names and the comparison substitutes them for the two sides' parameters.  The
handles are fresh, so the comparison's answer depends on the store having
them; con-leche's `canonNames` builds the same `Name` values, so the twin's
answer is con-leche's provided the interned handles denote those values — an
instance of `Bridge/StoreNested.lean`'s `EStore.internName` spec and of
`denoteN`'s injectivity, once each.
-/
import ConRon.Bridge.Checker.Hyp

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap — the generated
name list denotes con-leche's, and the handles are fresh.

`sorry`: `internName` at `n` successive `Name.num Name.anonymous i` values.
Task #97-P3-Checker's sorry list, item 14. -/
theorem canonNames_run {n : Nat} {r : List NIdx} {s s' : AState}
    (hok : StateOK s) (hrun : canonNames n s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      Frontend.denoteNList s'.store.ns r
        = some ((List.range n).map (fun i => ConLeche.Name.num .anonymous i)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Canon.lean:198-201 ConstantVal.canonEq — the
handle comparison is the term comparison.

`sorry`: `canonExprEq`'s fuel induction (the `RelV` shape: a `Bool` answer,
no target store, so `bridge_vcs [canonExprEq, RelV]` is the closer task
#97-P3-0 §5 measures at zero hand work per arm), plus `canonNames_run`.  Task
#97-P3-Checker's sorry list, item 14. -/
theorem IConstantVal.canonEq_run {cv cv' : IConstantVal} {c c' : ConstantVal}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hcv' : Frontend.denoteCV s.store cv' = some c')
    (hrun : IConstantVal.canonEq cv cv' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.ConstantVal.canonEq c c' := by
  sorry

/-- con-leche: ConLeche/Kernel/Canon.lean:251-253 ConstantInfo.canonEq —
**the pinned-block comparison**, at a whole stored constant.  This is what
`checkDecl`'s `.axiomDecl` arm runs on `Quot.sound` and what `basisPinHit`
runs on a block's members.

`sorry`: seven constructor arms over `IConstantVal.canonEq_run` and
`canonRulesEq`.  Task #97-P3-Checker's sorry list, item 14. -/
theorem IConstantInfo.canonEq_run {ci ci' : IConstantInfo} {c c' : ConstantInfo}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hci : Frontend.denoteCI s.store ci = some c)
    (hci' : Frontend.denoteCI s.store ci' = some c')
    (hrun : IConstantInfo.canonEq ci ci' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.ConstantInfo.canonEq c c' := by
  sorry

/-- con-leche: ConLeche/Kernel/Canon.lean:291-293 canonEqList — the same at a
block.

`sorry`: a list induction over `IConstantInfo.canonEq_run`.  Task
#97-P3-Checker's sorry list, item 14. -/
theorem canonEqList_run {cs cs' : List IConstantInfo}
    {xs xs' : List ConstantInfo} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hcs : Frontend.denoteCIList s.store cs = some xs)
    (hcs' : Frontend.denoteCIList s.store cs' = some xs')
    (hrun : canonEqList cs cs' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.canonEqList xs xs' := by
  sorry

end ConRon.Bridge
