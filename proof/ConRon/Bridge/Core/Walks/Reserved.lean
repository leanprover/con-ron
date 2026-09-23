/-
# `ConRon.Bridge.Core.Walks.Reserved` — the reserved-name list, for the Core tier

Task #97-P3-Core round 5.  `structUnitCert` and `structEtaCertWith` read
`Arena/Core.lean`'s `reservedBasisNames` (since twin fix D5, the pin-table
read `pinReserved`).  Its closed rule is `Bridge/Checker/Names.lean`'s
`reservedBasisNames_run`, and this tier first imported that module — until
task #97-P3-Checker round 9 made `Checker/Names.lean` import `Checker/Hyp.lean`,
which imports this tier's `Induction.lean`: a cycle.  The Checker lane is not
this tier's to edit, so the seven small pieces the chain needs are COPIED
here under `…C` names (so the two copies never clash when both modules meet
in one import closure): `pinAt_runC`, `PinStepC`, `internName_runC`,
`reservedBasisNames_runC` (now one `pinReserved_spec` read),
`denoteNL_toListC`, `denoteNList_containsC`.

**Ask for the Checker lane**: these belong below both tiers (they mention
nothing but `Bridge/Specs.lean`'s pin/intern triples and `StateOK.lean`'s
`denoteNL`); moved to a module both can import, this file shrinks to nothing.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Promote.Pers

open ConLeche ConRon.Arena

namespace ConRon.Bridge.Core

open ConRon.Bridge

set_option autoImplicit false

/-- con-leche: none — `pinAt` in run form (copy of `Bridge/Checker/Names.lean`'s
`pinAt_runC`, see the module note). -/
theorem pinAt_runC {i : Nat} {s s' : AState} {n : NIdx} {x : ConLeche.Name}
    (hp : PinsOK s) (hx : pinNames[i]? = some x)
    (hr : pinAt i s = .ok (n, s')) :
    s' = s ∧ denoteN s.store.ns n = some x := by
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ ∀ y, pinNames[i]? = some y →
      denoteN s.store.ns r = some y) rfl hr (pinAt_spec s i hp)
  exact ⟨h.1, h.2 x hx⟩

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

theorem PinStepC.trans {a b c : AState} (h₁ : PinStepC a b) (h₂ : PinStepC b c) :
    PinStepC a c :=
  ⟨h₂.wf, h₁.ext.trans h₂.ext, by rw [h₂.memos, h₁.memos],
    by rw [h₂.caches, h₁.caches], by rw [h₂.pins, h₁.pins]⟩

theorem PinStepC.pinsOK {s s' : AState} (h : PinStepC s s') (hp : PinsOK s) :
    PinsOK s' := hp.mono h.ext h.pins

/-- con-leche: none — `internName` in run form, off `Bridge/Specs.lean`'s
triple. -/
theorem internName_runC {nm : ConLeche.Name} {s s' : AState} {n : NIdx}
    (hwf : StoreWF s.store) (hr : internName nm s = .ok (n, s')) :
    PinStepC s s' ∧ denoteN s'.store.ns n = some nm := by
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => StoreWF t.store ∧ Ext s.store t.store ∧
        t.store.pers = s.store.pers ∧ t.store.scr = s.store.scr ∧
        t.store.scratchOn = s.store.scratchOn ∧
        t.memos = s.memos ∧ t.caches = s.caches ∧ t.pins = s.pins ∧
        denoteN t.store.ns r = some nm) rfl hr (internName_spec s nm hwf)
  obtain ⟨h1, h2, _, _, _, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h6, h7, h8⟩, h9⟩

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
**the nineteen reserved names, as handles that denote them**, off the pin
table (`pinReserved_spec`, twin fix D5 of task #97-T2-LOCKSTEP): the state
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

/-- con-leche: none — a handle `List.contains` is a name `List.contains`
(copy of `Bridge/Checker/Names.lean`'s `denoteNList_containsC`). -/
theorem denoteNList_containsC {st : EStore} (hwf : StoreWF st) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns ns = some xs →
      ∀ (n : NIdx) (x : ConLeche.Name), denoteN st.ns n = some x →
        ns.contains n = xs.contains x := by
  obtain ⟨rk, hrk⟩ := hwf
  have hns : NStoreWF st.ns := hrk.nsWF
  intro ns
  induction ns with
  | nil => intro xs h n x _; simp only [Frontend.denoteNList, Option.some.injEq] at h
           subst h; rfl
  | cons a as ih =>
    intro xs h n x hx
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        have hhead : (n == a) = (x == y) := by
          by_cases hae : a = n
          · subst hae
            rw [hx] at ha
            obtain rfl := Option.some.inj ha
            simp
          · have hae' : ¬ n = a := fun hh => hae hh.symm
            have hne' : ¬ x = y := by
              intro hxy; subst hxy
              exact hae (denoteN_inj hns ha hx)
            rw [beq_eq_false_iff_ne.mpr hae', beq_eq_false_iff_ne.mpr hne']
        simp only [List.contains_cons, hhead, ih ys has n x hx]

section Census

#print axioms pinAt_runC
#print axioms internName_runC
#print axioms reservedBasisNames_runC
#print axioms denoteNL_toListC
#print axioms denoteNList_containsC

end Census

end ConRon.Bridge.Core
