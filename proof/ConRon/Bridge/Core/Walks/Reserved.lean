/-
# `ConRon.Bridge.Core.Walks.Reserved` — the reserved-name list, for the Core tier

Task #97-P3-Core round 5.  `structUnitCert` and `structEtaCertWith` read
`Arena/Core.lean`'s `reservedBasisNames` (six pin reads, thirteen name
interns).  Its closed rule is `Bridge/Checker/Names.lean`'s
`reservedBasisNames_run`, and this tier first imported that module — until
task #97-P3-Checker round 9 made `Checker/Names.lean` import `Checker/Hyp.lean`,
which imports this tier's `Induction.lean`: a cycle.  The Checker lane is not
this tier's to edit, so the seven small pieces the chain needs are COPIED
here under `…C` names (so the two copies never clash when both modules meet
in one import closure): `pinAt_runC`, `PinStepC`, `internName_runC`,
`reservedBasisNames_runC` (the 1.4 s no-accumulator chain, verbatim),
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

set_option linter.constructorNameAsVariable false in
set_option linter.unusedVariables false in
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
**the nineteen reserved names, as handles that denote them.**  Six are pin
slots and thirteen are fresh interns, so the run appends; the frame is
`PinStepC` and the answer is `denoteNL` at con-leche's own list.

Nineteen steps of one shape: `pinAt_runC` reads the table and leaves the state
alone, `internName_runC` appends.

**No accumulator** (task #97-P3-Checker-3).  The round that wrote this carried
a running `denoteNL t.store (hs ++ [h]) (xs ++ [x])` across the chain, and
that one decision cost **57 of the module's 60 seconds**: the eighteen
`have acc…` lines doubled — 0.35 s, 0.6 s, 1.1 s, 2.1 s, 4.5 s, 8.3 s, 12.5 s
— and the closing `exact` spent 28.7 s more normalising a nineteen-deep
left-nested `List.append` against the literal the `do`-block returns.  Nothing
in the chain needs the partial lists: each step's `denoteN` is a fact of its
own, and the nineteen are assembled ONCE at the end, against the literal, with
a suffix chain of `Ext`s (`u₁ … u₁₈`) carrying each to the final store.  The
theorem is 1.4 s.

The general rule, and the reason it is written here: **never accumulate a
list-indexed invariant along a do-block chain.**  Carry the per-step facts and
build the list once — an accumulator makes every later step's term mention
every earlier step's list, which is quadratic at best, and pays for the
normalisation twice, once per `++`. -/
theorem reservedBasisNames_runC {s s' : AState} {hs : List NIdx}
    (hwf : StoreWF s.store) (hp : PinsOK s)
    (hr : reservedBasisNames s = .ok (hs, s')) :
    PinStepC s s' ∧ denoteNL s'.store hs reservedBasisNameValues := by
  simp only [Arena.reservedBasisNames] at hr
  have r0 := hr
  -- step 1 — `Eq`, off the pin table
  obtain ⟨h1, t1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨e1, d1⟩ := pinAt_runC (x := ConLeche.eqName) hp rfl g1
  rw [e1] at r1
  -- step 2 — `Eq.refl`, interned
  obtain ⟨h2, t2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨p2, d2⟩ := internName_runC hwf g2
  have k2 : PinStepC s t2 := p2
  have q2 : PinsOK t2 := p2.pinsOK hp
  -- step 3 — `Eq.rec`, interned
  obtain ⟨h3, t3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨p3, d3⟩ := internName_runC p2.wf g3
  have k3 : PinStepC s t3 := k2.trans p3
  have q3 : PinsOK t3 := p3.pinsOK q2
  -- steps 4-6 — `Nat`, `Nat.zero`, `Nat.succ`, off the pin table
  obtain ⟨h4, t4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨e4, d4⟩ := pinAt_runC (x := ConLeche.natName) q3 rfl g4
  rw [e4] at r4
  obtain ⟨h5, t5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨e5, d5⟩ := pinAt_runC (x := ConLeche.natZeroName) q3 rfl g5
  rw [e5] at r5
  obtain ⟨h6, t6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨e6, d6⟩ := pinAt_runC (x := ConLeche.natSuccName) q3 rfl g6
  rw [e6] at r6
  -- step 7 — `Nat.rec`, interned
  obtain ⟨h7, t7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨p7, d7⟩ := internName_runC p3.wf g7
  have k7 : PinStepC s t7 := k3.trans p7
  have q7 : PinsOK t7 := p7.pinsOK q3
  -- step 8 — `PUnit`, off the pin table
  obtain ⟨h8, t8, g8, r8⟩ := AM.bind_ok r7
  obtain ⟨e8, d8⟩ := pinAt_runC (x := ConLeche.punitName) q7 rfl g8
  rw [e8] at r8
  -- steps 9-18 — ten interns
  obtain ⟨h9, t9, g9, r9⟩ := AM.bind_ok r8
  obtain ⟨p9, d9⟩ := internName_runC p7.wf g9
  have k9 : PinStepC s t9 := k7.trans p9
  have q9 : PinsOK t9 := p9.pinsOK q7
  obtain ⟨h10, t10, g10, r10⟩ := AM.bind_ok r9
  obtain ⟨p10, d10⟩ := internName_runC p9.wf g10
  have k10 : PinStepC s t10 := k9.trans p10
  have q10 : PinsOK t10 := p10.pinsOK q9
  obtain ⟨h11, t11, g11, r11⟩ := AM.bind_ok r10
  obtain ⟨p11, d11⟩ := internName_runC p10.wf g11
  have k11 : PinStepC s t11 := k10.trans p11
  have q11 : PinsOK t11 := p11.pinsOK q10
  obtain ⟨h12, t12, g12, r12⟩ := AM.bind_ok r11
  obtain ⟨p12, d12⟩ := internName_runC p11.wf g12
  have k12 : PinStepC s t12 := k11.trans p12
  have q12 : PinsOK t12 := p12.pinsOK q11
  obtain ⟨h13, t13, g13, r13⟩ := AM.bind_ok r12
  obtain ⟨p13, d13⟩ := internName_runC p12.wf g13
  have k13 : PinStepC s t13 := k12.trans p13
  have q13 : PinsOK t13 := p13.pinsOK q12
  obtain ⟨h14, t14, g14, r14⟩ := AM.bind_ok r13
  obtain ⟨p14, d14⟩ := internName_runC p13.wf g14
  have k14 : PinStepC s t14 := k13.trans p14
  have q14 : PinsOK t14 := p14.pinsOK q13
  obtain ⟨h15, t15, g15, r15⟩ := AM.bind_ok r14
  obtain ⟨p15, d15⟩ := internName_runC p14.wf g15
  have k15 : PinStepC s t15 := k14.trans p15
  have q15 : PinsOK t15 := p15.pinsOK q14
  obtain ⟨h16, t16, g16, r16⟩ := AM.bind_ok r15
  obtain ⟨p16, d16⟩ := internName_runC p15.wf g16
  have k16 : PinStepC s t16 := k15.trans p16
  have q16 : PinsOK t16 := p16.pinsOK q15
  obtain ⟨h17, t17, g17, r17⟩ := AM.bind_ok r16
  obtain ⟨p17, d17⟩ := internName_runC p16.wf g17
  have k17 : PinStepC s t17 := k16.trans p17
  have q17 : PinsOK t17 := p17.pinsOK q16
  obtain ⟨h18, t18, g18, r18⟩ := AM.bind_ok r17
  obtain ⟨p18, d18⟩ := internName_runC p17.wf g18
  have k18 : PinStepC s t18 := k17.trans p18
  have q18 : PinsOK t18 := p18.pinsOK q17
  -- step 19 — `Quot.sound`, off the pin table
  obtain ⟨h19, t19, g19, r19⟩ := AM.bind_ok r18
  obtain ⟨e19, d19⟩ :=
    pinAt_runC (x := (ConLeche.quotName.str "sound")) q18 rfl g19
  rw [e19] at r19
  -- the suffix extensions: `uᵢ` carries a fact stated at `tᵢ` to the last
  -- state, and there are as many of them as there are interns
  have u18 : Ext t18.store t18.store := Ext.refl _
  have u17 : Ext t17.store t18.store := p18.ext
  have u16 : Ext t16.store t18.store := p17.ext.trans u17
  have u15 : Ext t15.store t18.store := p16.ext.trans u16
  have u14 : Ext t14.store t18.store := p15.ext.trans u15
  have u13 : Ext t13.store t18.store := p14.ext.trans u14
  have u12 : Ext t12.store t18.store := p13.ext.trans u13
  have u11 : Ext t11.store t18.store := p12.ext.trans u12
  have u10 : Ext t10.store t18.store := p11.ext.trans u11
  have u9 : Ext t9.store t18.store := p10.ext.trans u10
  have u7 : Ext t7.store t18.store := p9.ext.trans u9
  have u3 : Ext t3.store t18.store := p7.ext.trans u7
  have u2 : Ext t2.store t18.store := p3.ext.trans u3
  have u1 : Ext s.store t18.store := p2.ext.trans u2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r19
  exact ⟨k18, denoteN_ext d1 u1, denoteN_ext d2 u2, denoteN_ext d3 u3,
    denoteN_ext d4 u3, denoteN_ext d5 u3, denoteN_ext d6 u3,
    denoteN_ext d7 u7, denoteN_ext d8 u7, denoteN_ext d9 u9,
    denoteN_ext d10 u10, denoteN_ext d11 u11, denoteN_ext d12 u12,
    denoteN_ext d13 u13, denoteN_ext d14 u14, denoteN_ext d15 u15,
    denoteN_ext d16 u16, denoteN_ext d17 u17, d18, d19, trivial⟩

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
