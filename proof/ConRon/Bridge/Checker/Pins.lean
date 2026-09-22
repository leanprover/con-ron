/-
# `ConRon.Bridge.Checker.Pins` — the startup walk, and what it leaves behind

`Arena/Checker.lean`'s `internAllPins` is DESIGN §8.6 P2d's one-time tree
walk, run by the driver before the prelude with the scratch tier CLOSED.  This
module is what it leaves behind, and the three clauses are exactly the three
the fold carries:

| | |
|---|---|
| `PinsOK s` | the forty-nine `PIN_*` slots denote `pinNames`, the reserved list denotes `reservedBasisNameValues`, the three nullary values denote (`Bridge/StateOK.lean`) |
| `PersPins s` | **every pin handle is persistent** — task #97-P3-0 §7's "one more clause", the one that makes `PinsOK` survive `dropScratch` (`Bridge/Checker/Inv.lean`'s `PinsOK.pmono`) |
| `PinsDenote s.store pins pinsP` | the interned `Nat`-operation pin variants denote con-leche's (`Bridge/Checker/Decl.lean`) |

`Arena/Pins.lean`'s own module note states the obligation:

> **Denotation unchanged.**  A pin is `internName` of the same `Name`, so the
> handle this record holds is the handle `pin` computed before […].  The one
> obligation the bridge owes is an instance of `intern_spec`:
> `pinsOK st → st.pins.names[PIN_NAT] = (internName st natName).1`

and `PinsOK` is the strengthened form of it: not that the handle is the one
`intern` would give, but that it DENOTES the right name, which is what every
consumer actually reads.

**Why the persistence clause is free.**  `internReservedPins` runs before the
parse, so `s.store.scratchOn = false` at the call; `intern`'s persistent
branch is the only one reachable, and every handle it produces has the
persistent tier bit.  The hypothesis below is therefore `s.store.scratchOn =
false` and nothing else.
-/
import ConRon.Bridge.Checker.Decl

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-119 reservedBasisNames —
**the pin table, filled**: `internReservedPins` on a store with the scratch
tier closed leaves the table denoting and persistent.

`sorry`: `internNameList` over `Bridge/StoreNested.lean`'s
`EStore.internName` spec (49 + 19 interns), then `internLsNode` / `internLNode`
/ `internSortE` over `Bridge/Specs.lean`'s.  The persistence half is the
`scratchOn = false` branch of `intern`, which `Arena/WFProofs.lean`'s
`intern_view_spec` already exposes.  Task #97-P3-Checker's sorry list,
item 13. -/
theorem internReservedPins_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false)
    (hrun : internReservedPins s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsOK s' ∧ PersPins s' ∧
      s'.store.scratchOn = false ∧ s'.memos = s.memos ∧ s'.caches = s.caches := by
  sorry

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _ — **the pin variants,
interned**: `internPinSets` on a closed scratch tier hands back a list that
denotes its argument, variant by variant, in persistent handles.

`sorry`: sixteen `Frontend.internExpr` calls per variant, over the frontend
tier's intern exactness (`denoteE (internExpr e) = some e`), and the list
recursion.  Task #97-P3-Checker's sorry list, item 13. -/
theorem internPinSets_run {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false)
    (hrun : internPinSets ps s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsDenote s'.store r ps ∧
      PersPinSets r ∧ s'.store.scratchOn = false ∧ s'.pins = s.pins ∧
      s'.caches = s.caches ∧ s'.memos = s.memos := by
  sorry

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
**THE STARTUP WALK**: `internAllPins` interns every datum the checker compares
a stream record against, and hands back the interned pin list.  Its
postcondition is the fold's precondition — `PinsOK`, `PersPins`,
`PinsDenote`, `PersPinSets` — which is why the capstone
(`Bridge/Checker/Capstone.lean`) can take those four as hypotheses and the
driver tier can discharge all four here.

**`internAllPins` does NOT establish `PinsOK`** — `internReservedPins` does,
and the driver runs it first (`Arena/Main.lean`).  So `PinsOK` and `PersPins`
are hypotheses here and travel through: the walk only appends, and
`PinsOK.mono` carries them.

**The per-call frame** (asked for by the Frontend tier, task
#97-P3-Checker-2): the walk touches the four stores and the pin record and
NOTHING else, so `s'.caches = s.caches` and `s'.memos = s.memos` come out
with the rest.  `Bridge/Frontend/Capstone.lean`'s
`no_False_declaration_pipeline` needs them for the `internAllPins` call
`runPipelineM` makes between `preparePrelude` and `installThenCheck`.

`sorry`: twenty-nine pin reads (each with a `@[spec]` theorem already in
`Bridge/Specs.lean`) composed with `internPinSets_run`.  Task
#97-P3-Checker's sorry list, item 13. -/
theorem internAllPins_run {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hpp : PersPins s)
    (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsOK s' ∧ PersPins s' ∧
      PinsDenote s'.store r ps ∧ PersPinSets r ∧
      s'.store.scratchOn = false ∧
      s'.caches = s.caches ∧ s'.memos = s.memos := by
  sorry

end ConRon.Bridge
