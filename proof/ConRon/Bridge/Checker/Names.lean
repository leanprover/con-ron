/-
# `ConRon.Bridge.Checker.Names` — the reserved-name list, and the two readers
under it

**Why this module exists** (task #97-P3-Layout).  `reservedBasisNames_run`
below is read by two tiers that do not see each other.  The checker tier's
`Bridge/Checker/Base.lean` uses it for `checkConstantVal_bridge`'s second
guard; the inductive tier's `Bridge/Inductives/StructParts.lean` needs it for
`structPartsCore?_spec`, `structPartsCore?_isSome` and `nativeShape?_spec` —
`structPartsCore?` tests `reserved.contains T`, `reserved.contains C` and
`reserved.contains cvR.name`, and `nativeShape?` tests two of the same.  It
used to live in `Base.lean`, which `Bridge/Inductives/**` does not import and
must not (the checker tier's `.indDecl` arm imports the inductive tier back),
so those three statements were blocked on an import wall with no missing
proof (task #97-P3-Ind round 5, §R5.5 item 1).

Restating it in the inductive tier was not an option: round 3 of the checker
tier measured `reservedBasisNames_run` at **63 seconds** in its first shape,
and the note on the theorem below is where that lesson is written down.  So
the theorem moved DOWN instead, to the one place both tiers already see —
`Bridge/Checker/Inv.lean` plus `Bridge/Specs.lean`, which is the common
prefix of `Bridge/Checker/Hyp.lean` (what `Base.lean` imports) and of
`Bridge/Inductives/Rel.lean`'s imports.

**What came with it**, because none of it can be restated any more cheaply
than the theorem itself:

| | |
|---|---|
| `pinAt_run` | the pin-table reader — six of the nineteen steps |
| `PinStep` and its three laws | the frame every step shares |
| `internName_run` | the intern — thirteen of the nineteen steps |
| `denoteNL_snoc` | the shape the note forbids, kept because the fact is right |
| `denoteNL_toList`, `reservedBasisNameValues_eq` | the two equations a CONSUMER of the answer needs |
| `denoteNList_contains` | and the third: a handle `List.contains` is a name `List.contains` |

Nothing else moved and no proof changed: `Base.lean` imports this module, so
every one of its old readers still reads the same theorem.
-/
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Specs

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The pin-table reader -/

/-- con-leche: none — `pinAt` in run form, off `Bridge/Specs.lean`'s triple.

It sat beside `PinStep` until round 4, which moved it above
`constsResolve_run` (whose literal arms read pins); task #97-P3-Layout brought
it back down here with the chain that needs it, and `Base.lean` imports this
module, so `constsResolve_run` still sees it. -/
theorem pinAt_run {i : Nat} {s s' : AState} {n : NIdx} {x : ConLeche.Name}
    (hp : PinsOK s) (hx : pinNames[i]? = some x)
    (hr : pinAt i s = .ok (n, s')) :
    s' = s ∧ denoteN s.store.ns n = some x := by
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ ∀ y, pinNames[i]? = some y →
      denoteN s.store.ns r = some y) rfl hr (pinAt_spec s i hp)
  exact ⟨h.1, h.2 x hx⟩
/-! ## The reserved-name list, interned

`Arena/Core.lean`'s `reservedBasisNames` is not `Arena/Pins.lean`'s
`pinReserved`: it reads six names off the pin table and INTERNS the other
thirteen, so it appends to the arena and its spec is an `Ext` rather than a
state equation.  The two halves are `Bridge/Specs.lean`'s `pinAt_spec` (which
consumes `PinsOK`) and `internName_spec` (which is closed), and the chain
re-establishes `PinsOK` after every append.

`PinStep` is the frame all nineteen steps share, so the chain is nineteen
lines of the same shape. -/

/-- con-leche: none — one more denoting handle at the end of a denoting list.

The chain below no longer uses it: an accumulated `hs ++ [h]` is what made
`reservedBasisNames_run` a 63-second theorem (see its note), so the rule for
this tier is to carry the per-step facts and assemble the list once.  It is
kept because the fact itself is right, and because the rule is easier to state
next to the shape it forbids. -/
theorem denoteNL_snoc {st : EStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name) (h : NIdx) (x : ConLeche.Name),
      denoteNL st hs xs → denoteN st.ns h = some x →
        denoteNL st (hs ++ [h]) (xs ++ [x]) := by
  intro hs
  induction hs with
  | nil =>
    intro xs h x hd hn
    cases xs with
    | nil => exact ⟨hn, trivial⟩
    | cons _ _ => exact hd.elim
  | cons a as ih =>
    intro xs h x hd hn
    cases xs with
    | nil => exact hd.elim
    | cons y ys => exact ⟨hd.1, ih ys h x hd.2 hn⟩

/-- con-leche: none — the frame a pin read or a name intern leaves: the store
only grew, and nothing else moved. -/
structure PinStep (s s' : AState) : Prop where
  wf : StoreWF s'.store
  ext : Ext s.store s'.store
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem PinStep.refl {s : AState} (h : StoreWF s.store) : PinStep s s :=
  ⟨h, Ext.refl _, rfl, rfl, rfl⟩

theorem PinStep.trans {a b c : AState} (h₁ : PinStep a b) (h₂ : PinStep b c) :
    PinStep a c :=
  ⟨h₂.wf, h₁.ext.trans h₂.ext, by rw [h₂.memos, h₁.memos],
    by rw [h₂.caches, h₁.caches], by rw [h₂.pins, h₁.pins]⟩

theorem PinStep.pinsOK {s s' : AState} (h : PinStep s s') (hp : PinsOK s) :
    PinsOK s' := hp.mono h.ext h.pins

/-- con-leche: none — `internName` in run form, off `Bridge/Specs.lean`'s
triple. -/
theorem internName_run {nm : ConLeche.Name} {s s' : AState} {n : NIdx}
    (hwf : StoreWF s.store) (hr : internName nm s = .ok (n, s')) :
    PinStep s s' ∧ denoteN s'.store.ns n = some nm := by
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
`PinStep` and the answer is `denoteNL` at con-leche's own list.

Nineteen steps of one shape: `pinAt_run` reads the table and leaves the state
alone, `internName_run` appends.

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
theorem reservedBasisNames_run {s s' : AState} {hs : List NIdx}
    (hwf : StoreWF s.store) (hp : PinsOK s)
    (hr : reservedBasisNames s = .ok (hs, s')) :
    PinStep s s' ∧ denoteNL s'.store hs reservedBasisNameValues := by
  simp only [Arena.reservedBasisNames] at hr
  have r0 := hr
  -- step 1 — `Eq`, off the pin table
  obtain ⟨h1, t1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.eqName) hp rfl g1
  rw [e1] at r1
  -- step 2 — `Eq.refl`, interned
  obtain ⟨h2, t2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨p2, d2⟩ := internName_run hwf g2
  have k2 : PinStep s t2 := p2
  have q2 : PinsOK t2 := p2.pinsOK hp
  -- step 3 — `Eq.rec`, interned
  obtain ⟨h3, t3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨p3, d3⟩ := internName_run p2.wf g3
  have k3 : PinStep s t3 := k2.trans p3
  have q3 : PinsOK t3 := p3.pinsOK q2
  -- steps 4-6 — `Nat`, `Nat.zero`, `Nat.succ`, off the pin table
  obtain ⟨h4, t4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.natName) q3 rfl g4
  rw [e4] at r4
  obtain ⟨h5, t5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.natZeroName) q3 rfl g5
  rw [e5] at r5
  obtain ⟨h6, t6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.natSuccName) q3 rfl g6
  rw [e6] at r6
  -- step 7 — `Nat.rec`, interned
  obtain ⟨h7, t7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨p7, d7⟩ := internName_run p3.wf g7
  have k7 : PinStep s t7 := k3.trans p7
  have q7 : PinsOK t7 := p7.pinsOK q3
  -- step 8 — `PUnit`, off the pin table
  obtain ⟨h8, t8, g8, r8⟩ := AM.bind_ok r7
  obtain ⟨e8, d8⟩ := pinAt_run (x := ConLeche.punitName) q7 rfl g8
  rw [e8] at r8
  -- steps 9-18 — ten interns
  obtain ⟨h9, t9, g9, r9⟩ := AM.bind_ok r8
  obtain ⟨p9, d9⟩ := internName_run p7.wf g9
  have k9 : PinStep s t9 := k7.trans p9
  have q9 : PinsOK t9 := p9.pinsOK q7
  obtain ⟨h10, t10, g10, r10⟩ := AM.bind_ok r9
  obtain ⟨p10, d10⟩ := internName_run p9.wf g10
  have k10 : PinStep s t10 := k9.trans p10
  have q10 : PinsOK t10 := p10.pinsOK q9
  obtain ⟨h11, t11, g11, r11⟩ := AM.bind_ok r10
  obtain ⟨p11, d11⟩ := internName_run p10.wf g11
  have k11 : PinStep s t11 := k10.trans p11
  have q11 : PinsOK t11 := p11.pinsOK q10
  obtain ⟨h12, t12, g12, r12⟩ := AM.bind_ok r11
  obtain ⟨p12, d12⟩ := internName_run p11.wf g12
  have k12 : PinStep s t12 := k11.trans p12
  have q12 : PinsOK t12 := p12.pinsOK q11
  obtain ⟨h13, t13, g13, r13⟩ := AM.bind_ok r12
  obtain ⟨p13, d13⟩ := internName_run p12.wf g13
  have k13 : PinStep s t13 := k12.trans p13
  have q13 : PinsOK t13 := p13.pinsOK q12
  obtain ⟨h14, t14, g14, r14⟩ := AM.bind_ok r13
  obtain ⟨p14, d14⟩ := internName_run p13.wf g14
  have k14 : PinStep s t14 := k13.trans p14
  have q14 : PinsOK t14 := p14.pinsOK q13
  obtain ⟨h15, t15, g15, r15⟩ := AM.bind_ok r14
  obtain ⟨p15, d15⟩ := internName_run p14.wf g15
  have k15 : PinStep s t15 := k14.trans p15
  have q15 : PinsOK t15 := p15.pinsOK q14
  obtain ⟨h16, t16, g16, r16⟩ := AM.bind_ok r15
  obtain ⟨p16, d16⟩ := internName_run p15.wf g16
  have k16 : PinStep s t16 := k15.trans p16
  have q16 : PinsOK t16 := p16.pinsOK q15
  obtain ⟨h17, t17, g17, r17⟩ := AM.bind_ok r16
  obtain ⟨p17, d17⟩ := internName_run p16.wf g17
  have k17 : PinStep s t17 := k16.trans p17
  have q17 : PinsOK t17 := p17.pinsOK q16
  obtain ⟨h18, t18, g18, r18⟩ := AM.bind_ok r17
  obtain ⟨p18, d18⟩ := internName_run p17.wf g18
  have k18 : PinStep s t18 := k17.trans p18
  have q18 : PinsOK t18 := p18.pinsOK q17
  -- step 19 — `Quot.sound`, off the pin table
  obtain ⟨h19, t19, g19, r19⟩ := AM.bind_ok r18
  obtain ⟨e19, d19⟩ :=
    pinAt_run (x := (ConLeche.quotName.str "sound")) q18 rfl g19
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

/-! ## The name-list denotation, as a function -/

/-- con-leche: none — `denoteNL` (the relation `PinsOK` is stated with) and
`Frontend.denoteNList` (the function everything else is stated with) are the
same fact. -/
theorem denoteNL_toList {st : EStore} :
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

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-119 reservedBasisNames —
the arena's copy of the reserved list IS con-leche's, on the nose. -/
theorem reservedBasisNameValues_eq :
    reservedBasisNameValues = ConLeche.reservedBasisNames := rfl
/-! ## The name-list denotation, at a membership test -/

/-- con-leche: none — **a handle comparison is a name comparison, at a LIST**:
`List.contains` over handles answers what `List.contains` over the denoted
names answers.  Both directions are needed and they come from different
places — `denoteN` is a function (handles equal ⇒ names equal) and it is
INJECTIVE (names equal ⇒ handles equal), which is DESIGN §8.3's soundness
obligation cashed. -/
theorem denoteNList_contains {st : EStore} (hwf : StoreWF st) :
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
