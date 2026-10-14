/-
# `ConRon.Bridge.Core.Walks.Reserved` — the reserved-name list, for the Core tier

`structUnitCert` and `structEtaCertWith` read `Arena/Core.lean`'s
`reservedBasisNames` (the pin-table read `pinReserved`).  Its rule is
`Bridge/Checker/Names.lean`'s `reservedBasisNames_run`, which this tier cannot
import: `Checker/Names.lean` imports `Checker/Hyp.lean`, which imports this
tier's `Induction.lean`.  So the small pieces the chain needs are COPIED here
under `…C` names (so the two copies never clash when both modules meet in one
import closure): `PinStepC`, `reservedBasisNames_runC` (one
`pinReserved_spec` read), `denoteNL_toListC` (the list membership test,
`denoteNList_contains`, is `Bridge/Grind.lean`'s).

These belong below both tiers (they mention nothing but `Bridge/Specs.lean`'s
pin/intern triples and `StateOK.lean`'s `denoteNL`); in a module both can
import, this file would shrink to nothing.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Promote.Pers

open ConLeche ConRon.Arena

namespace ConRon.Bridge.Core

open ConRon.Bridge

set_option autoImplicit false

/-- con-leche: none — the frame a pin read or a name intern leaves: the store
only grew, and nothing else moved. -/
structure PinStepC (s s' : AState) : Prop where
  wf : StoreWF s'.store
  ext : Ext s.store s'.store
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem PinStepC.refl {s : AState} (h : StoreWF s.store) : PinStepC s s :=
  ⟨h, Ext.refl _, rfl, rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
**the nineteen reserved names, as handles that denote them**, off the pin
table (`pinReserved_spec`, twin fix D5, DESIGN `### Task #97-T2-LOCKSTEP`): the state
does not move, so the frame is `PinStepC.refl`. -/
theorem reservedBasisNames_runC {s s' : AState} {hs : List NIdx}
    (hwf : StoreWF s.store) (hp : PinsOK s)
    (hr : reservedBasisNames s = .ok (hs, s')) :
    PinStepC s s' ∧ denoteNL s'.store hs reservedBasisNameValues := by
  simp only [Arena.reservedBasisNames] at hr
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteNL s.store r reservedBasisNameValues)
    rfl hr (pinReserved_spec s hp)
  obtain ⟨rfl, hd⟩ := h
  exact ⟨PinStepC.refl hwf, hd⟩

/-- con-leche: none — `denoteNL` and `Frontend.denoteNList` are the same fact
(copy of `Bridge/Checker/Names.lean`'s `denoteNL_toListC`). -/
theorem denoteNL_toListC {st : EStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      denoteNL st hs xs → Frontend.denoteNList st.ns hs = some xs := by
  intro hs
  induction hs with
  | nil => intro xs h; cases xs with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons a as ih =>
    intro xs h
    cases xs with
    | nil => exact h.elim
    | cons y ys =>
      simp only [Frontend.denoteNList, h.1, ih ys h.2]

section Census

#print axioms reservedBasisNames_runC
#print axioms denoteNL_toListC

end Census

end ConRon.Bridge.Core
