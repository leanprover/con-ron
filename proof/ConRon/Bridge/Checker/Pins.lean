/-
# `ConRon.Bridge.Checker.Pins` — the startup walk, and what it leaves behind

`Arena/Checker.lean`'s `internAllPins` is DESIGN §8.6 P2d's one-time tree
walk, run by the driver before the prelude with the scratch tier CLOSED.  This
module is what it leaves behind, and the three clauses are exactly the three
the fold carries:

| | |
|---|---|
| `PinsOK s` | the forty-nine `PIN_*` slots denote `pinNames`, the reserved list denotes `reservedBasisNameValues`, the three nullary values denote, and **the zero name handle decodes to `.anonymous`** (`Bridge/StateOK.lean`; the last clause is task #97-P3-Ind round 5's, and this theorem is its debtor — see `PinsOK.anon`) |
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

**Why this module imports the frontend tier** (task #97-P3-Layout).
`internAllPins` interns whole `ConstantInfo`s, and the exactness of
`internCI` / `internCV` / `internExpr` is
`Bridge/Frontend/Shared.lean`'s — eighteen reads of it in the walk below.
That file used to sit ABOVE this one, because `Bridge/Frontend/Rel.lean`
imported `Bridge/Checker.lean` whole for three names that live in
`Bridge/Checker/Inv.lean`.  With that import narrowed, the frontend tier's
bottom is below the checker tier and this import is the right way round.
-/
import ConRon.Bridge.Checker.Decl
import ConRon.Bridge.Frontend.Shared
import ConRon.Bridge.Checker.DeclVal

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: none — `Arena/Pins.lean`'s own `internNameList` (the pin
table's cursor recursion, a sibling of the frontend's) denotes its argument,
in the scratch-agnostic frame. -/
theorem internNameList_pins_sstep : ∀ (ns : List ConLeche.Name) {s s' : AState}
    {hs : List NIdx}, StateOK s →
    ConRon.Arena.internNameList ns s = .ok (hs, s') →
    Frontend.IStepS s s' ∧ Frontend.denoteNList s'.store.ns hs = some ns := by
  intro ns
  induction ns with
  | nil =>
    intro s s' hs hok hrun
    rw [ConRon.Arena.internNameList] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst; subst hv
    exact ⟨Frontend.IStepS.refl hok, rfl⟩
  | cons a as ih =>
    intro s s' hs hok hrun
    rw [ConRon.Arena.internNameList] at hrun
    obtain ⟨h1, s₁, hn, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hstep1, hdn⟩ := Frontend.internName_sstep hok hn
    obtain ⟨t1, s₂, hns, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨hstep2, hdns⟩ := ih hstep1.ok hns
    obtain ⟨hv, hst⟩ := AM.pure_ok hrest2
    subst hst; subst hv
    refine ⟨hstep1.trans hstep2, ?_⟩
    simp only [Frontend.denoteNList, denoteN_ext hdn hstep2.ext, hdns]

/-- con-leche: none — the list readback, as the pointwise relation `PinsOK`
states. -/
theorem denoteNL_of_denoteNList {st : EStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns hs = some xs → denoteNL st hs xs := by
  intro hs
  induction hs with
  | nil =>
    intro xs h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; trivial
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨ha, ih ys has⟩

/-- con-leche: none — a level-list handle that denotes on a closed store is
persistent (`PersN_of_view`'s twin at the level-list store). -/
theorem PersLs_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {h : LsIdx} {xs : List Level}
    (hd : denoteLs st.lss h = some xs) : PersLs h := by
  obtain ⟨us, hv, -⟩ := denoteLs_view hd
  by_cases hp : h.isPersistent = true
  · exact hp
  · exfalso
    rw [Arena.LsStore.view, if_neg hp,
      if_neg (by rw [(Frontend.scratchOn_nested hwf).1, hoff]; simp)] at hv
    exact absurd hv (by simp)

/-- con-leche: none — **the zero name handle is `.anonymous`** once the pin
names are interned: every pin name is a `.str`/`.num` chain bottoming out at
`.anonymous`, so `.anonymous` sits in the persistent `anons` table, whose only
slot is 0, and `Idx.ofWord 0` is tag-`anonymous`, tier-persistent, slot 0
(`PinsOK.anon`'s doc comment is the argument).

`sorry`: the chain's last link through `Arena.denoteN_view`, then the `anons`
table's single slot — a fact about `Arena/Store.lean`'s name tables, one
round. -/
theorem denoteN_default_of_pinNames {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {hs : List NIdx}
    (hd : Frontend.denoteNList st.ns hs = some pinNames) :
    denoteN st.ns (default : NIdx) = some ConLeche.Name.anonymous := by
  -- 1. some handle views as `.anonymous`: the first pin name's chain
  have hchain : ∀ (f : Nat) (i : NIdx) (n : ConLeche.Name),
      Arena.denoteNAux st.ns f i = some n → ∃ a, st.ns.view a = some .anonymous := by
    intro f
    induction f with
    | zero => intro i n h; simp [Arena.denoteNAux] at h
    | succ k ih =>
      intro i n h
      simp only [Arena.denoteNAux, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, h⟩ := h
      cases v with
      | anonymous => exact ⟨i, hv⟩
      | str p s =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨q, hq, -⟩ := h
        exact ih p q hq
      | num p m =>
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨q, hq, -⟩ := h
        exact ih p q hq
  obtain ⟨a, ha⟩ : ∃ a, st.ns.view a = some .anonymous := by
    cases hs with
    | nil => simp [Frontend.denoteNList, pinNames] at hd
    | cons h0 hs0 =>
      simp only [Frontend.denoteNList] at hd
      cases h0d : denoteN st.ns h0 with
      | none => rw [h0d] at hd; simp at hd
      | some x => exact hchain _ h0 x h0d
  -- 2. it is persistent, so the persistent `anons` table is non-empty
  have hpa : a.isPersistent = true := Frontend.PersN_of_view hwf hoff ha
  have hnode : ∃ x, st.ns.pers.anons.node? 0 = some x := by
    simp only [Arena.NStore.view, hpa, if_true, Arena.NTables.get] at ha
    by_cases ht : (a.tag == NTag.anonymous) = true
    · rw [if_pos ht, Option.map_eq_some_iff] at ha
      obtain ⟨x, hx, -⟩ := ha
      simp only [Arena.Tbl.node?] at hx ⊢
      have hlt : a.idxNat < st.ns.pers.anons.nodes.size :=
        (Array.getElem?_eq_some_iff.mp hx).1
      exact ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    · rw [if_neg ht] at ha
      split at ha
      · simp at ha
      · split at ha <;> simp at ha
  obtain ⟨x, hx⟩ := hnode
  -- 3. the zero word is that slot
  have hv0 : st.ns.view (default : NIdx) = some .anonymous := by
    have hp0 : (default : NIdx).isPersistent = true := by decide
    have ht0 : ((default : NIdx).tag == NTag.anonymous) = true := by decide
    have hi0 : (default : NIdx).idxNat = 0 := by decide
    simp only [Arena.NStore.view, hp0, if_true, Arena.NTables.get, ht0, hi0, hx,
      Option.map_some]
  simp only [Arena.denoteN, Arena.denoteNAux, hv0, Option.bind_some]

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-119 reservedBasisNames —
**the pin table, filled**: `internReservedPins` on a store with the scratch
tier closed leaves the table denoting and persistent.

**SKELETONISED** (task #97-P3-Checker round 8): proved from the frontend
tier's `IStepS` leaves (`internNameList_pins_sstep`, `internLsNode_sstep`,
`internLNode_sstep`, `internE_sstep`) — persistence off `Pers…_of_denote` at
the closed store, `PersLs_of_denote` new — and ONE child,
`denoteN_default_of_pinNames` (`PinsOK.anon`: the zero name handle is
`.anonymous`, a fact about the persistent `anons` table). -/
theorem internReservedPins_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false)
    (hrun : internReservedPins s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsOK s' ∧ PersPins s' ∧
      s'.store.scratchOn = false ∧ s'.memos = s.memos ∧ s'.caches = s.caches := by
  simp only [Arena.internReservedPins] at hrun
  obtain ⟨hs, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨st1, hd1⟩ := internNameList_pins_sstep pinNames hok g1
  obtain ⟨rs, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨st2, hd2⟩ := internNameList_pins_sstep reservedBasisNameValues st1.ok g2
  obtain ⟨us, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨st3, hd3⟩ := Frontend.internLsNode_sstep st2.ok
    (by intro c hc; simp at hc) g3
  obtain ⟨z, s4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨st4, hd4⟩ := Frontend.internLNode_sstep st3.ok
    ⟨by intro c hc; simp [LNodeView.lchildren] at hc,
     by intro c hc; simp [LNodeView.nchildren] at hc⟩ g4
  have hz4 : denoteL s4.store.ls z = some .zero := by rw [hd4]; rfl
  obtain ⟨o, s5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨st5, hd5⟩ := Frontend.internLNode_sstep st4.ok
    ⟨by intro c hc
        simp only [LNodeView.lchildren, List.mem_singleton] at hc
        subst hc; exact lview_isSome_of_denote hz4,
     by intro c hc; simp [LNodeView.nchildren] at hc⟩ g5
  have ho5 : denoteL s5.store.ls o = some (.succ .zero) := by
    rw [hd5]; simp only [denoteLView, denoteL_ext hz4 st5.ext, Option.map_some]
  obtain ⟨e1, s6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨st6, hd6⟩ := Frontend.internE_sstep st5.ok
    (viewOK_sort (lview_isSome_of_denote ho5)) g6
  have he6 : denoteE s6.store e1 = some (.sort (.succ .zero)) := by
    rw [hd6]; simp only [denoteEView, denoteL_ext ho5 st6.ext, Option.map_some]
  obtain ⟨g, s7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨hg, hs7⟩ : g = s6 ∧ s7 = s6 := by
    simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at g7
    exact ⟨g7.1.symm, g7.2.symm⟩
  subst g
  subst s7
  simp only [set, MonadStateOf.set, StateT.set, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at r7
  obtain ⟨-, rfl⟩ := r7
  have hacc := ((((st1.trans st2).trans st3).trans st4).trans st5).trans st6
  have hoff6 : s6.store.scratchOn = false := hacc.off hoff
  have hwf6 := st6.ok.wf
  have hx26 : Ext s2.store s6.store := ((st3.ext.trans st4.ext).trans st5.ext).trans st6.ext
  have hx16 : Ext s1.store s6.store := st2.ext.trans hx26
  have hdn1 := denoteNListE_ext hx16 _ _ hd1
  have hdn2 := denoteNListE_ext hx26 _ _ hd2
  have hus6 : denoteLs s6.store.lss us = some [] := by
    have : denoteLs s3.store.lss us = some [] := by rw [hd3]; rfl
    exact denoteLs_ext this ((st4.ext.trans st5.ext).trans st6.ext)
  have hz6 := denoteL_ext hz4 (st5.ext.trans st6.ext)
  refine ⟨⟨hwf6⟩, hacc.ext, ?_, ?_, hoff6, hacc.memos, hacc.caches⟩
  · exact
      { ready := by
          show hs.toArray.size = pinCount
          rw [List.size_toArray, denoteNList_length _ _ hdn1]; rfl
        names := by
          show denoteNL s6.store hs.toArray.toList pinNames
          rw [List.toList_toArray]; exact denoteNL_of_denoteNList _ _ hdn1
        reserved := denoteNL_of_denoteNList _ _ hdn2
        emptyLevels := hus6
        zeroLevel := hz6
        sortOne := he6
        anon := denoteN_default_of_pinNames hwf6 hoff6 hdn1 }
  · exact
      { names := by
          intro n hn
          rw [List.mem_toArray] at hn
          exact Frontend.PersNList_of_denote hwf6 hoff6 hdn1 n hn
        reserved := Frontend.PersNList_of_denote hwf6 hoff6 hdn2
        emptyLevels := PersLs_of_denote hwf6 hoff6 hus6
        zeroLevel := Frontend.PersL_of_denote hwf6 hoff6 hz6
        sortOne := Frontend.PersE_of_denote hwf6 hoff6 he6 }

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _ — ONE pin variant,
interned: sixteen `internExpr`/`internExprList` calls, each an `IStepS` link
(`Frontend.internExpr_sstep`, `Frontend.internExprList_sstep` at a fresh
memo), every denotation transported to the final store. -/
theorem internPinSet_sstep {ps : NatOpPinSet} {p : INatOpPinSet} {s s' : AState}
    (hok : StateOK s) (hrun : ConRon.Arena.internPinSet ps s = .ok (p, s')) :
    Frontend.IStepS s s' ∧ PinSetDenote s'.store p ps := by
  have iE : ∀ {a b : AState} {e : Expr} {h : EIdx}, StateOK a →
      ConRon.Arena.internExpr e a = .ok (h, b) →
      Frontend.IStepS a b ∧ denoteE b.store h = some e :=
    fun hok hr => Frontend.internExpr_sstep hok hr
  have iL : ∀ {a b : AState} {es : List Expr} {hs : List EIdx}, StateOK a →
      ConRon.Arena.internExprList es a = .ok (hs, b) →
      Frontend.IStepS a b ∧ Frontend.denoteEList b.store hs = some es := by
    intro a b es hs hok hr
    simp only [ConRon.Arena.internExprList] at hr
    obtain ⟨q, a1, hg, hr2⟩ := AM.bind_ok hr
    obtain ⟨hv, hst⟩ := AM.pure_ok hr2
    subst hst; subst hv
    obtain ⟨hs1, hd, -⟩ :=
      Frontend.internExprList_sstep es hok (Frontend.EMemoOK.empty a.store) hg
    exact ⟨hs1, hd⟩
  simp only [ConRon.Arena.internPinSet] at hrun
  obtain ⟨x1, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨t1, d1⟩ := iE hok g1
  obtain ⟨x2, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨t2, d2⟩ := iE t1.ok g2
  obtain ⟨x3, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨t3, d3⟩ := iE t2.ok g3
  obtain ⟨x4, s4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨t4, d4⟩ := iE t3.ok g4
  obtain ⟨x5, s5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨t5, d5⟩ := iE t4.ok g5
  obtain ⟨x6, s6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨t6, d6⟩ := iE t5.ok g6
  obtain ⟨x7, s7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨t7, d7⟩ := iE t6.ok g7
  obtain ⟨x8, s8, g8, r8⟩ := AM.bind_ok r7
  obtain ⟨t8, d8⟩ := iE t7.ok g8
  obtain ⟨x9, s9, g9, r9⟩ := AM.bind_ok r8
  obtain ⟨t9, d9⟩ := iL t8.ok g9
  obtain ⟨x10, s10, g10, r10⟩ := AM.bind_ok r9
  obtain ⟨t10, d10⟩ := iL t9.ok g10
  obtain ⟨x11, s11, g11, r11⟩ := AM.bind_ok r10
  obtain ⟨t11, d11⟩ := iL t10.ok g11
  obtain ⟨x12, s12, g12, r12⟩ := AM.bind_ok r11
  obtain ⟨t12, d12⟩ := iL t11.ok g12
  obtain ⟨x13, s13, g13, r13⟩ := AM.bind_ok r12
  obtain ⟨t13, d13⟩ := iL t12.ok g13
  obtain ⟨x14, s14, g14, r14⟩ := AM.bind_ok r13
  obtain ⟨t14, d14⟩ := iL t13.ok g14
  obtain ⟨x15, s15, g15, r15⟩ := AM.bind_ok r14
  obtain ⟨t15, d15⟩ := iL t14.ok g15
  obtain ⟨x16, s16, g16, r16⟩ := AM.bind_ok r15
  obtain ⟨t16, d16⟩ := iL t15.ok g16
  obtain ⟨hv, hst⟩ := AM.pure_ok r16
  subst hst; subst hv
  have e16 : Ext s'.store s'.store := Ext.refl _
  have e15 : Ext s15.store s'.store := t16.ext.trans e16
  have e14 : Ext s14.store s'.store := t15.ext.trans e15
  have e13 : Ext s13.store s'.store := t14.ext.trans e14
  have e12 : Ext s12.store s'.store := t13.ext.trans e13
  have e11 : Ext s11.store s'.store := t12.ext.trans e12
  have e10 : Ext s10.store s'.store := t11.ext.trans e11
  have e9 : Ext s9.store s'.store := t10.ext.trans e10
  have e8 : Ext s8.store s'.store := t9.ext.trans e9
  have e7 : Ext s7.store s'.store := t8.ext.trans e8
  have e6 : Ext s6.store s'.store := t7.ext.trans e7
  have e5 : Ext s5.store s'.store := t6.ext.trans e6
  have e4 : Ext s4.store s'.store := t5.ext.trans e5
  have e3 : Ext s3.store s'.store := t4.ext.trans e4
  have e2 : Ext s2.store s'.store := t3.ext.trans e3
  have e1 : Ext s1.store s'.store := t2.ext.trans e2
  refine ⟨(((((((((((((((t1).trans t2).trans t3).trans t4).trans t5).trans t6).trans t7).trans t8).trans t9).trans t10).trans t11).trans t12).trans t13).trans t14).trans t15).trans t16, ?_⟩
  exact
    { toolchain := rfl
      divPin := e1.expr _ _ d1
      modPin := e2.expr _ _ d2
      gcdPin := e3.expr _ _ d3
      landPin := e4.expr _ _ d4
      lorPin := e5.expr _ _ d5
      xorPin := e6.expr _ _ d6
      shiftLeftPin := e7.expr _ _ d7
      shiftRightPin := e8.expr _ _ d8
      divProofs := denoteEList_ext e9 _ _ d9
      modProofs := denoteEList_ext e10 _ _ d10
      gcdProofs := denoteEList_ext e11 _ _ d11
      landProofs := denoteEList_ext e12 _ _ d12
      lorProofs := denoteEList_ext e13 _ _ d13
      xorProofs := denoteEList_ext e14 _ _ d14
      shiftLeftProofs := denoteEList_ext e15 _ _ d15
      shiftRightProofs := denoteEList_ext e16 _ _ d16 }

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _ — the variant list,
interned: the list recursion over `internPinSet_sstep`. -/
theorem internPinSets_sstep : ∀ (ps : List NatOpPinSet) {r : List INatOpPinSet}
    {s s' : AState}, StateOK s → ConRon.Arena.internPinSets ps s = .ok (r, s') →
    Frontend.IStepS s s' ∧ PinsDenote s'.store r ps := by
  intro ps
  induction ps with
  | nil =>
    intro r s s' hok hrun
    rw [ConRon.Arena.internPinSets] at hrun
    obtain ⟨hv, hst⟩ := AM.pure_ok hrun
    subst hst; subst hv
    exact ⟨Frontend.IStepS.refl hok, trivial⟩
  | cons q qs ih =>
    intro r s s' hok hrun
    rw [ConRon.Arena.internPinSets] at hrun
    obtain ⟨p, s₁, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨t1, d1⟩ := internPinSet_sstep hok g1
    obtain ⟨ps', s₂, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨t2, d2⟩ := ih t1.ok g2
    obtain ⟨hv, hst⟩ := AM.pure_ok r2
    subst hst; subst hv
    exact ⟨t1.trans t2, (PinsDenote.mono t2.ext [p] [q] ⟨d1, trivial⟩).1, d2⟩

/-- con-leche: none — a pin variant that denotes on a closed store is
persistent (`Pers…_of_denote`, clause by clause). -/
theorem PersPinSet_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) {p : INatOpPinSet} {q : NatOpPinSet}
    (h : PinSetDenote st p q) : PersPinSet p := by
  have hE := fun {x : EIdx} {e : Expr} (hd : denoteE st x = some e) =>
    Frontend.PersE_of_denote hwf hoff hd
  have hL := fun {xs : List EIdx} {es : List Expr}
    (hd : Frontend.denoteEList st xs = some es) =>
    Frontend.PersEList_of_denote hwf hoff hd
  refine ⟨?_, ?_⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hE h.divPin
    · exact hE h.modPin
    · exact hE h.gcdPin
    · exact hE h.landPin
    · exact hE h.lorPin
    · exact hE h.xorPin
    · exact hE h.shiftLeftPin
    · exact hE h.shiftRightPin
  · intro e he
    simp only [List.mem_append] at he
    rcases he with ((((((he | he) | he) | he) | he) | he) | he) | he
    · exact hL h.divProofs e he
    · exact hL h.modProofs e he
    · exact hL h.gcdProofs e he
    · exact hL h.landProofs e he
    · exact hL h.lorProofs e he
    · exact hL h.xorProofs e he
    · exact hL h.shiftLeftProofs e he
    · exact hL h.shiftRightProofs e he

/-- con-leche: none — the same, list-wise. -/
theorem PersPinSets_of_denote {st : EStore} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) :
    ∀ {r : List INatOpPinSet} {ps : List NatOpPinSet},
      PinsDenote st r ps → PersPinSets r
  | [], _, _ => fun _ h => absurd h (by simp)
  | _ :: _, [], h => h.elim
  | p :: r, q :: ps, h => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact PersPinSet_of_denote hwf hoff h.1
    · exact PersPinSets_of_denote hwf hoff h.2 x hx


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
  obtain ⟨hst, hd⟩ := internPinSets_sstep ps hok hrun
  have hoff' := hst.off hoff
  exact ⟨hst.ok, hst.ext, hd, PersPinSets_of_denote hst.ok.wf hoff' hd, hoff',
    hst.pins, hst.caches, hst.memos⟩

/-- con-leche: ConLeche/Kernel/Basis.lean:41-66 BasisKind.decls — the raw
pinned block's intern, as one scratch-agnostic step. -/
theorem BasisKind.decls_sstep {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s) (hrun : BasisKind.decls k s = .ok (r, s')) :
    Frontend.IStepS s s' := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst
  exact (Frontend.internCIList_sstep (ConLeche.BasisKind.decls k) hok
    (Frontend.EMemoOK.empty s.store) hgo).1

/-- con-leche: ConLeche/Kernel/BasisA.lean:51-57 BasisKind.declsA — the
annotated pinned block's intern, as one scratch-agnostic step. -/
theorem BasisKind.declsA_sstep {k : BasisKind} {r : List IConstantInfo}
    {s s' : AState} (hok : StateOK s)
    (hrun : BasisKind.declsA k s = .ok (r, s')) : Frontend.IStepS s s' := by
  simp only [ConRon.Arena.BasisKind.declsA, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst
  exact (Frontend.internCIList_sstep (ConLeche.BasisKind.declsA k) hok
    (Frontend.EMemoOK.empty s.store) hgo).1

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:72-73 reduceOpNames — two pin
reads; the state is left alone. -/
theorem reduceOpNames_state {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : reduceOpNames s = .ok (ns, s')) : s' = s := by
  simp only [Arena.reduceOpNames] at hr
  obtain ⟨a, u0, q0, w0⟩ := AM.bind_ok hr
  obtain ⟨p0, -⟩ := pinAt_run (x := ConLeche.reduceNatName) hp rfl q0
  rw [p0] at w0
  obtain ⟨b, u1, q1, w1⟩ := AM.bind_ok w0
  obtain ⟨p1, -⟩ := pinAt_run (x := ConLeche.reduceBoolName) hp rfl q1
  rw [p1] at w1
  exact (AM.pure_ok w1).2

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the startup walk's reserved-name step, in the scratch-agnostic frame: since
twin fix D5 it is the pin-table read `pinReserved`, which leaves the state
alone (`pinReserved_spec`). -/
theorem reservedBasisNames_sstep {s s' : AState} {hs : List NIdx}
    (hst : StateOK s) (hp : PinsOK s)
    (hr : reservedBasisNames s = .ok (hs, s')) : Frontend.IStepS s s' := by
  simp only [Arena.reservedBasisNames] at hr
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteNL s.store r reservedBasisNameValues)
    rfl hr (pinReserved_spec s hp)
  obtain ⟨rfl, -⟩ := h
  exact Frontend.IStepS.refl hst

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

**PROVED** (task #97-P3-Checker round 8), relative to `internPinSets_run`:
thirty-six links, each a scratch-agnostic `IStepS` — the twelve basis blocks
(`BasisKind.decls_sstep` / `declsA_sstep`), eighteen fresh-memo interns
(`internCI_fresh`, `internCV_fresh`, `Frontend.internExpr_sstep`),
`reservedBasisNames_sstep` (a table read since twin fix D5), and six pin
reads that leave the state alone —
then `internPinSets_run` for the variants.  `PersPins` travels because the pin
record is untouched and persistence is a fact about handles. -/
theorem internAllPins_run {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hpp : PersPins s)
    (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ PinsOK s' ∧ PersPins s' ∧
      PinsDenote s'.store r ps ∧ PersPinSets r ∧
      s'.store.scratchOn = false ∧
      s'.caches = s.caches ∧ s'.memos = s.memos := by
  simp only [Arena.internAllPins] at hrun
  have a0 : Frontend.IStepS s s := Frontend.IStepS.refl hok
  obtain ⟨_, u0, q0, w0⟩ := AM.bind_ok hrun
  have a1 := a0.trans (BasisKind.decls_sstep a0.ok q0)
  obtain ⟨_, u1, q1, w1⟩ := AM.bind_ok w0
  have a2 := a1.trans (BasisKind.declsA_sstep a1.ok q1)
  obtain ⟨_, u2, q2, w2⟩ := AM.bind_ok w1
  have a3 := a2.trans (BasisKind.decls_sstep a2.ok q2)
  obtain ⟨_, u3, q3, w3⟩ := AM.bind_ok w2
  have a4 := a3.trans (BasisKind.declsA_sstep a3.ok q3)
  obtain ⟨_, u4, q4, w4⟩ := AM.bind_ok w3
  have a5 := a4.trans (BasisKind.decls_sstep a4.ok q4)
  obtain ⟨_, u5, q5, w5⟩ := AM.bind_ok w4
  have a6 := a5.trans (BasisKind.declsA_sstep a5.ok q5)
  obtain ⟨_, u6, q6, w6⟩ := AM.bind_ok w5
  have a7 := a6.trans (BasisKind.decls_sstep a6.ok q6)
  obtain ⟨_, u7, q7, w7⟩ := AM.bind_ok w6
  have a8 := a7.trans (BasisKind.declsA_sstep a7.ok q7)
  obtain ⟨_, u8, q8, w8⟩ := AM.bind_ok w7
  have a9 := a8.trans (BasisKind.decls_sstep a8.ok q8)
  obtain ⟨_, u9, q9, w9⟩ := AM.bind_ok w8
  have a10 := a9.trans (BasisKind.declsA_sstep a9.ok q9)
  obtain ⟨_, u10, q10, w10⟩ := AM.bind_ok w9
  have a11 := a10.trans (BasisKind.decls_sstep a10.ok q10)
  obtain ⟨_, u11, q11, w11⟩ := AM.bind_ok w10
  have a12 := a11.trans (BasisKind.declsA_sstep a11.ok q11)
  obtain ⟨_, u12, q12, w12⟩ := AM.bind_ok w11
  have a13 := a12.trans (internCI_fresh a12.ok q12).1
  obtain ⟨_, u13, q13, w13⟩ := AM.bind_ok w12
  have a14 := a13.trans (internCI_fresh a13.ok q13).1
  obtain ⟨_, u14, q14, w14⟩ := AM.bind_ok w13
  have a15 := a14.trans (internCI_fresh a14.ok q14).1
  obtain ⟨_, u15, q15, w15⟩ := AM.bind_ok w14
  have a16 := a15.trans (internCI_fresh a15.ok q15).1
  obtain ⟨_, u16, q16, w16⟩ := AM.bind_ok w15
  have a17 := a16.trans (internCI_fresh a16.ok q16).1
  obtain ⟨_, u17, q17, w17⟩ := AM.bind_ok w16
  have a18 := a17.trans (internCI_fresh a17.ok q17).1
  obtain ⟨_, u18, q18, w18⟩ := AM.bind_ok w17
  have a19 := a18.trans (internCV_fresh a18.ok q18).1
  obtain ⟨_, u19, q19, w19⟩ := AM.bind_ok w18
  have a20 := a19.trans (internCV_fresh a19.ok q19).1
  obtain ⟨_, u20, q20, w20⟩ := AM.bind_ok w19
  have a21 := a20.trans (internCV_fresh a20.ok q20).1
  obtain ⟨_, u21, q21, w21⟩ := AM.bind_ok w20
  have a22 := a21.trans (internCV_fresh a21.ok q21).1
  obtain ⟨_, u22, q22, w22⟩ := AM.bind_ok w21
  have a23 := a22.trans (internCV_fresh a22.ok q22).1
  obtain ⟨_, u23, q23, w23⟩ := AM.bind_ok w22
  have a24 := a23.trans (internCV_fresh a23.ok q23).1
  obtain ⟨_, u24, q24, w24⟩ := AM.bind_ok w23
  have a25 := a24.trans (internCV_fresh a24.ok q24).1
  obtain ⟨_, u25, q25, w25⟩ := AM.bind_ok w24
  have a26 := a25.trans (internCV_fresh a25.ok q25).1
  obtain ⟨_, u26, q26, w26⟩ := AM.bind_ok w25
  have a27 := a26.trans (internCV_fresh a26.ok q26).1
  obtain ⟨_, u27, q27, w27⟩ := AM.bind_ok w26
  have a28 := a27.trans (internCV_fresh a27.ok q27).1
  obtain ⟨_, u28, q28, w28⟩ := AM.bind_ok w27
  have a29 := a28.trans (Frontend.internExpr_sstep a28.ok q28).1
  obtain ⟨_, u29, q29, w29⟩ := AM.bind_ok w28
  have a30 := a29.trans (Frontend.internExpr_sstep a29.ok q29).1
  obtain ⟨_, u30, q30, w30⟩ := AM.bind_ok w29
  have a31 := a30.trans (reservedBasisNames_sstep a30.ok (hpins.mono a30.ext a30.pins) q30)
  obtain ⟨_, u31, q31, w31⟩ := AM.bind_ok w30
  obtain ⟨rfl, -⟩ := natOpNames_run (hpins.mono a31.ext a31.pins) q31
  have a32 := a31
  obtain ⟨_, u32, q32, w32⟩ := AM.bind_ok w31
  obtain ⟨rfl, -⟩ := natDivModNames_run (hpins.mono a32.ext a32.pins) q32
  have a33 := a32
  obtain ⟨_, u33, q33, w33⟩ := AM.bind_ok w32
  obtain rfl := reduceOpNames_state (hpins.mono a33.ext a33.pins) q33
  have a34 := a33
  obtain ⟨_, u34, q34, w34⟩ := AM.bind_ok w33
  obtain ⟨p34, -⟩ := pinAt_run (x := ConLeche.sorryAxName) (hpins.mono a34.ext a34.pins) rfl q34
  rw [p34] at w34
  have a35 := a34
  obtain ⟨_, u35, q35, w35⟩ := AM.bind_ok w34
  obtain ⟨p35, -⟩ := pinAt_run (x := ConLeche.quotSoundName) (hpins.mono a35.ext a35.pins) rfl q35
  rw [p35] at w35
  have a36 := a35
  obtain ⟨hst', hx', hden, hpps, hoff', hpe, hce, hme⟩ :=
    internPinSets_run a36.ok (by rw [a36.scratch]; exact hoff) w35
  have hpeq : s'.pins = s.pins := by rw [hpe, a36.pins]
  refine ⟨hst', a36.ext.trans hx', hpins.mono (a36.ext.trans hx') hpeq, ?_, hden,
    hpps, hoff', by rw [hce, a36.caches], by rw [hme, a36.memos]⟩
  exact ⟨by rw [hpeq]; exact hpp.names, by rw [hpeq]; exact hpp.reserved,
    by rw [hpeq]; exact hpp.emptyLevels, by rw [hpeq]; exact hpp.zeroLevel,
    by rw [hpeq]; exact hpp.sortOne⟩

end ConRon.Bridge
