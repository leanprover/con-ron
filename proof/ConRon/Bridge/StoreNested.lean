/-
# `ConRon.Bridge.StoreNested` — the three nested interns' store specs

**The one obligation task #97a's frozen store API left open**, named by task
#97b's "For P2c" list:

> `EStore.internName` / `internLevel` / `internLevels` have no spec.  P2a
> froze them without one; every `Core` body that interns a name or a level
> will need `Ext` and `StoreWF` for them, and so does `instLPFast`.

`Arena/WFProofs.lean` proves `{N,L,Ls}Store.intern_spec` — the push preserves
that store's own invariant, extends it, and the new handle decodes — and
`EStore.intern_spec` for an EXPRESSION node.  What is missing is the LIFT: an
`EStore` whose nested store grew is still well formed, and its `Ext` holds.

The three statements are below.  They are the shape every consumer needs, so
they are stated here whether or not they are proved here; the two facts that
make them cheap are `Arena/WFProofs.lean`'s

* `EStore.wf_of_scr_empty`'s hypothesis list, which already isolates exactly
  the six nested-store facts `EWFAt` reads (`hnsv`/`hlv`/`hlsv` for the
  views, `hnsd`/`hld`/`hlsd` for the derived columns) — a nested intern
  leaves every one of them alone at a handle that already decoded, which is
  `NTables.derAt_push_of_get` and its two siblings;
* `denoteEAux_store_mono`, which wants `st'.lss = st.lss` and therefore needs
  ONE generalisation — the nested-store version, whose three hypotheses are
  the `LsExt` conjuncts.

The `EStore` node tables (`pers`, `scr`, `bms`) and the `scratchOn` flags are
literally unchanged by all three, so `view`, `derived`, `find?`, `findBM` and
`nodeCount` at the expression level do not move; the whole content is the
nested store's own `intern_spec` plus the six transports above.

## How it is proved (task #97-P3-0)

Each of the three interns is ONE field update as a value
(`EStore.internName_eq` and its two siblings), so the file is four layers:

1. `{N,L,Ls}Store.scratchOn_intern` and `{N,L,Ls}Store.derived_intern` — a
   push leaves the scratch flag alone and leaves the derived column alone at
   every handle that already decoded (`NTables.derAt_push_of_get` and its
   siblings);
2. `LStore.wf_of_ns`, `LsStore.wf_of_ls`, `EStore.wf_of_lss` — the
   `wf_of_scr_empty` shape with the *nested* store as the thing that moved
   instead of the scratch tier, so `pers`/`scr`/`scratchOn` are equal by
   `rfl` and the only clauses with content are the ones that read the store
   below (`nchildOK`/`lchildOK`/`lschildOK`), `derExact` (through
   `derOfView`, which reads the nested derived columns) and `sync`;
3. the `Ext` conjunct, which is `Arena/WFProofs.lean`'s own
   `EStore.internName_ext` / `internLevel_ext` / `internLevels_ext` (task
   #97a follow-up 4).  This file used to carry its own
   `denoteLAux_store_mono_nested` / `denoteEAux_store_mono_nested` and
   `LExt.of_ns` / `LsExt.of_ls` / `Ext.of_lss` lifts; the store layer now
   states the same fact UNCONDITIONALLY and over an arbitrary result store
   (`{N,L,Ls,}Ext.of_view_mono`), so the copies here were deleted;
4. the three statements themselves: each is `{N,L,Ls}Store.intern_spec` plus
   that conjunct plus `denote*_unfold` for the new handle's denotation.
-/
import ConRon.Bridge.Rel

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The nested interns, spelled out

Each lifted `intern` detaches the nested store before handing it down and puts
it back afterwards (DESIGN §8.4 lesson 14), so as a *value* it is a single
field update — which is what makes every expression-level read below `rfl`. -/

/-- con-leche: none — `EStore.internName` is one field update: the name store
interns, everything above it is copied. -/
theorem EStore.internName_eq (st : EStore) (v : NNodeView) :
    st.internName v =
      ({ st with lss := { st.lss with
          ls := { st.ls with ns := (st.ns.intern v).1 } } }, (st.ns.intern v).2) :=
  rfl

/-- con-leche: none — `EStore.internLevel` is one field update. -/
theorem EStore.internLevel_eq (st : EStore) (v : LNodeView) :
    st.internLevel v =
      ({ st with lss := { st.lss with ls := (st.ls.intern v).1 } },
        (st.ls.intern v).2) :=
  rfl

/-- con-leche: none — `EStore.internLevels` is one field update. -/
theorem EStore.internLevels_eq (st : EStore) (v : LsNodeView) :
    st.internLevels v =
      ({ st with lss := (st.lss.intern v).1 }, (st.lss.intern v).2) :=
  rfl

/-! ## What a push does NOT move: the flag and the derived column

`intern` never touches `scratchOn`, and `derAt` at an index the tier already
held is `Tbl.derAt_push_of_lt` — so the derived column stands still at every
handle that decoded before the push. -/

/-- con-leche: none — interning a name leaves the scratch flag alone. -/
theorem NStore.scratchOn_intern (st : NStore) (w : NNodeView) :
    (st.intern w).1.scratchOn = st.scratchOn := by
  simp only [NStore.intern]
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

/-- con-leche: none — interning a level leaves the scratch flag alone. -/
theorem LStore.scratchOn_intern (st : LStore) (w : LNodeView) :
    (st.intern w).1.scratchOn = st.scratchOn := by
  simp only [LStore.intern]
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

/-- con-leche: none — interning a level list leaves the scratch flag alone. -/
theorem LsStore.scratchOn_intern (st : LsStore) (w : LsNodeView) :
    (st.intern w).1.scratchOn = st.scratchOn := by
  simp only [LsStore.intern]
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

/-- con-leche: none — interning a name leaves the derived column alone at
every handle that already decoded. -/
theorem NStore.derived_intern {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk)
    (w : NNodeView) {i : NIdx} {v : NNodeView} (hv : st.view i = some v) :
    (st.intern w).1.derived i = st.derived i := by
  simp only [NStore.intern]
  split
  · rfl
  · split
    · rename_i hon
      split
      · rfl
      · by_cases hp : i.isPersistent = true
        · simp only [NStore.derived, hp, if_true]
        · have hp' : i.isPersistent = false := by simpa using hp
          have hget : st.scr.get i = some v := by
            rw [← NStore.view_scr hp' hon]; exact hv
          simp only [NStore.derived, hp', hon, if_true, Bool.false_eq_true,
            if_false]
          exact NTables.derAt_push_of_get h.sizedS hget
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      by_cases hp : i.isPersistent = true
      · have hget : st.pers.get i = some v := by
          rw [← NStore.view_pers hp]; exact hv
        simp only [NStore.derived, hp, if_true]
        exact NTables.derAt_push_of_get h.sizedP hget
      · have hp' : i.isPersistent = false := by simpa using hp
        simp only [NStore.derived, hp', hoff', Bool.false_eq_true, if_false]

/-- con-leche: none — interning a level leaves the derived column alone at
every handle that already decoded. -/
theorem LStore.derived_intern {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk)
    (w : LNodeView) {i : LIdx} {v : LNodeView} (hv : st.view i = some v) :
    (st.intern w).1.derived i = st.derived i := by
  simp only [LStore.intern]
  split
  · rfl
  · split
    · rename_i hon
      split
      · rfl
      · by_cases hp : i.isPersistent = true
        · simp only [LStore.derived, hp, if_true]
        · have hp' : i.isPersistent = false := by simpa using hp
          have hget : st.scr.get i = some v := by
            rw [← LStore.view_scr hp' hon]; exact hv
          simp only [LStore.derived, hp', hon, if_true, Bool.false_eq_true,
            if_false]
          exact LTables.derAt_push_of_get h.sizedS hget
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      by_cases hp : i.isPersistent = true
      · have hget : st.pers.get i = some v := by
          rw [← LStore.view_pers hp]; exact hv
        simp only [LStore.derived, hp, if_true]
        exact LTables.derAt_push_of_get h.sizedP hget
      · have hp' : i.isPersistent = false := by simpa using hp
        simp only [LStore.derived, hp', hoff', Bool.false_eq_true, if_false]

/-- con-leche: none — interning a level list leaves the derived column alone
at every handle that already decoded. -/
theorem LsStore.derived_intern {st : LsStore} (h : LsWF st) (w : LsNodeView)
    {i : LsIdx} {v : LsNodeView} (hv : st.view i = some v) :
    (st.intern w).1.derived i = st.derived i := by
  simp only [LsStore.intern]
  split
  · rfl
  · split
    · rename_i hon
      split
      · rfl
      · by_cases hp : i.isPersistent = true
        · simp only [LsStore.derived, hp, if_true]
        · have hp' : i.isPersistent = false := by simpa using hp
          have hget : st.scr.get i = some v := by
            rw [← LsStore.view_scr hp' hon]; exact hv
          simp only [LsStore.derived, hp', hon, if_true, Bool.false_eq_true,
            if_false]
          exact LsTables.derAt_push_of_get h.sizedS hget
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      by_cases hp : i.isPersistent = true
      · have hget : st.pers.get i = some v := by
          rw [← LsStore.view_pers hp]; exact hv
        simp only [LsStore.derived, hp, if_true]
        exact LsTables.derAt_push_of_get h.sizedP hget
      · have hp' : i.isPersistent = false := by simpa using hp
        simp only [LsStore.derived, hp', hoff', Bool.false_eq_true, if_false]

/-! ## The invariant, lifted through one level of the nesting -/

/-- con-leche: none — a level store whose NAME store grew is still well
formed at the same rank. -/
theorem LStore.wf_of_ns {st : LStore} {ns' : NStore} {rk : LIdx → Nat}
    (h : LWFAt st rk) (hwf : NStoreWF ns')
    (hon : ns'.scratchOn = st.ns.scratchOn)
    (hview : ∀ (c : NIdx) (u : NNodeView), st.ns.view c = some u →
      ns'.view c = some u)
    (hder : ∀ (c : NIdx) (u : NNodeView), st.ns.view c = some u →
      ns'.derived c = st.ns.derived c) :
    LWFAt { st with ns := ns' } rk := by
  refine { ns := hwf, childOK := h.childOK, nchildOK := ?nchildOK,
           rankP := h.rankP, rankS := h.rankS, consP := h.consP,
           consS := h.consS, fresh := h.fresh, derExact := ?derExact,
           sizedP := h.sizedP, sizedS := h.sizedS, capP := h.capP,
           capS := h.capS, scrOff := h.scrOff,
           sync := h.sync.trans hon.symm }
  case nchildOK =>
    intro i v hi c hc
    have hi' : st.view i = some v := hi
    have hch := h.nchildOK i v hi' c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hch.1
    refine ⟨?_, hch.2⟩
    have hc' : ns'.view c = some u := hview c u hu
    rw [hc']
    rfl
  case derExact =>
    intro i v hi
    have hi' : st.view i = some v := hi
    rw [LStore.derOfView_congr (st := st) (st' := { st with ns := ns' })
      (fun _ _ => rfl)
      (fun c hc => by
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (h.nchildOK i v hi' c hc).1
        exact hder c u hu)]
    exact h.derExact i v hi'

/-- con-leche: none — a level-list store whose LEVEL store grew is still well
formed. -/
theorem LsStore.wf_of_ls {st : LsStore} {ls' : LStore} (h : LsWF st)
    (hwf : LStoreWF ls') (hon : ls'.scratchOn = st.ls.scratchOn)
    (hview : ∀ (c : LIdx) (u : LNodeView), st.ls.view c = some u →
      ls'.view c = some u)
    (hder : ∀ (c : LIdx) (u : LNodeView), st.ls.view c = some u →
      ls'.derived c = st.ls.derived c) :
    LsWF { st with ls := ls' } := by
  refine { ls := hwf, lchildOK := ?lchildOK, consP := h.consP, consS := h.consS,
           fresh := h.fresh, derExact := ?derExact, sizedP := h.sizedP,
           sizedS := h.sizedS, capP := h.capP, capS := h.capS,
           scrOff := h.scrOff, sync := h.sync.trans hon.symm }
  case lchildOK =>
    intro i v hi c hc
    have hi' : st.view i = some v := hi
    have hch := h.lchildOK i v hi' c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hch.1
    refine ⟨?_, hch.2⟩
    have hc' : ls'.view c = some u := hview c u hu
    rw [hc']
    rfl
  case derExact =>
    intro i v hi
    have hi' : st.view i = some v := hi
    rw [LsStore.derOfView_congr (st := st) (st' := { st with ls := ls' }) v
      (fun c hc => by
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (h.lchildOK i v hi' c hc).1
        exact hder c u hu)]
    exact h.derExact i v hi'

/-- con-leche: none — an expression store whose LEVEL-LIST store grew is
still well formed at the same rank.  This is `EStore.wf_of_scr_empty` with the
nested store, not the scratch tier, as the thing that moved: its six
nested-store facts are exactly the hypotheses here, and a nested push needs
them at every handle that decodes, not only at the persistent ones. -/
theorem EStore.wf_of_lss {st : EStore} {lss' : LsStore} {rk : EIdx → Nat}
    (h : EWFAt st rk) (hwf : LsStoreWF lss')
    (hon : lss'.scratchOn = st.lss.scratchOn)
    (hnv : ∀ (c : NIdx) (u : NNodeView), st.ns.view c = some u →
      lss'.ls.ns.view c = some u)
    (hlv : ∀ (c : LIdx) (u : LNodeView), st.ls.view c = some u →
      lss'.ls.view c = some u)
    (hlsv : ∀ (c : LsIdx) (u : LsNodeView), st.lss.view c = some u →
      lss'.view c = some u)
    (hnd : ∀ (c : NIdx) (u : NNodeView), st.ns.view c = some u →
      lss'.ls.ns.derived c = st.ns.derived c)
    (hld : ∀ (c : LIdx) (u : LNodeView), st.ls.view c = some u →
      lss'.ls.derived c = st.ls.derived c)
    (hlsd : ∀ (c : LsIdx) (u : LsNodeView), st.lss.view c = some u →
      lss'.derived c = st.lss.derived c) :
    EWFAt { st with lss := lss' } rk := by
  refine { lss := hwf, childOK := h.childOK, nchildOK := ?nchildOK,
           lchildOK := ?lchildOK, lschildOK := ?lschildOK, rankP := h.rankP,
           rankS := h.rankS, bmChildOK := h.bmChildOK, consP := h.consP,
           consS := h.consS, fresh := h.fresh, bmConsP := h.bmConsP,
           bmConsS := h.bmConsS, bmFresh := h.bmFresh, bmKeyP := h.bmKeyP,
           bmKeyS := h.bmKeyS, derExact := ?derExact,
           bmDerExact := h.bmDerExact, sizedP := h.sizedP, sizedS := h.sizedS,
           capP := h.capP, capS := h.capS, bmCapP := h.bmCapP,
           bmCapS := h.bmCapS, scrOff := h.scrOff,
           sync := h.sync.trans hon.symm }
  case nchildOK =>
    intro i v hi c hc
    have hi' : st.view i = some v := hi
    have hch := h.nchildOK i v hi' c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hch.1
    exact ⟨Option.isSome_iff_exists.mpr ⟨u, hnv c u hu⟩, hch.2⟩
  case lchildOK =>
    intro i v hi c hc
    have hi' : st.view i = some v := hi
    have hch := h.lchildOK i v hi' c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hch.1
    exact ⟨Option.isSome_iff_exists.mpr ⟨u, hlv c u hu⟩, hch.2⟩
  case lschildOK =>
    intro i v hi c hc
    have hi' : st.view i = some v := hi
    have hch := h.lschildOK i v hi' c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hch.1
    exact ⟨Option.isSome_iff_exists.mpr ⟨u, hlsv c u hu⟩, hch.2⟩
  case derExact =>
    intro i v hi
    have hi' : st.view i = some v := hi
    rw [EStore.derOfView_congr (st := st) (st' := { st with lss := lss' })
      (fun _ _ => rfl)
      (fun c hc => by
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (h.nchildOK i v hi' c hc).1
        exact hnd c u hu)
      (fun c hc => by
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (h.lchildOK i v hi' c hc).1
        exact hld c u hu)
      (fun c hc => by
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (h.lschildOK i v hi' c hc).1
        exact hlsd c u hu)]
    exact h.derExact i v hi'

/-! ## The three specs -/

/-- con-leche: none — interning a NAME through the nesting keeps the whole
arena well formed, extends it, and leaves every expression-level read alone. -/
theorem EStore.internName_spec {st : EStore} {w : NNodeView} (h : StoreWF st)
    (hv : st.ns.ViewOK w) (hcap : st.ns.capOK w) :
    StoreWF (st.internName w).1 ∧ Ext st (st.internName w).1 ∧
      (st.internName w).1.pers = st.pers ∧
      (st.internName w).1.scr = st.scr ∧
      (st.internName w).1.scratchOn = st.scratchOn ∧
      (st.internName w).1.ns.view (st.internName w).2 = some w ∧
      denoteN (st.internName w).1.ns (st.internName w).2 =
        denoteNView (st.internName w).1.ns w := by
  obtain ⟨rk, h⟩ := h
  have hlsw : LsWF st.lss := h.lss
  obtain ⟨rkl, hlw⟩ : ∃ r, LWFAt st.lss.ls r := hlsw.ls
  obtain ⟨rkn, hnw⟩ : ∃ r, NWFAt st.lss.ls.ns r := hlw.ns
  obtain ⟨hnwf', -, hnview⟩ := NStore.intern_spec ⟨rkn, hnw⟩ hv hcap
  obtain ⟨rkn', hnw'⟩ := hnwf'
  have hlw' : LWFAt { st.ls with ns := (st.ns.intern w).1 } rkl :=
    LStore.wf_of_ns hlw ⟨rkn', hnw'⟩ (NStore.scratchOn_intern st.ns w)
      (fun _ _ hu => NStore.view_intern_mono st.ns w hu)
      (fun _ _ hu => NStore.derived_intern hnw w hu)
  have hlsw' :
      LsWF { st.lss with ls := { st.ls with ns := (st.ns.intern w).1 } } :=
    LsStore.wf_of_ls hlsw ⟨rkl, hlw'⟩ rfl (fun _ _ hu => hu) (fun _ _ _ => rfl)
  have hewf : EWFAt { st with lss :=
      { st.lss with ls := { st.ls with ns := (st.ns.intern w).1 } } } rk :=
    EStore.wf_of_lss h hlsw' rfl
      (fun _ _ hu => NStore.view_intern_mono st.ns w hu)
      (fun _ _ hu => hu) (fun _ _ hu => hu)
      (fun _ _ hu => NStore.derived_intern hnw w hu)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  rw [EStore.internName_eq]
  exact ⟨⟨rk, hewf⟩, EStore.internName_ext st w, rfl, rfl, rfl,
    hnview, denoteN_unfold hnw' hnview⟩

/-- con-leche: none — the same for a LEVEL node. -/
theorem EStore.internLevel_spec {st : EStore} {w : LNodeView} (h : StoreWF st)
    (hv : st.ls.ViewOK w) (hcap : st.ls.capOK w) :
    StoreWF (st.internLevel w).1 ∧ Ext st (st.internLevel w).1 ∧
      (st.internLevel w).1.pers = st.pers ∧
      (st.internLevel w).1.scr = st.scr ∧
      (st.internLevel w).1.scratchOn = st.scratchOn ∧
      (st.internLevel w).1.ls.view (st.internLevel w).2 = some w ∧
      denoteL (st.internLevel w).1.ls (st.internLevel w).2 =
        denoteLView (st.internLevel w).1.ls w := by
  obtain ⟨rk, h⟩ := h
  have hlsw : LsWF st.lss := h.lss
  obtain ⟨rkl, hlw⟩ : ∃ r, LWFAt st.lss.ls r := hlsw.ls
  obtain ⟨hlwf', -, hlview⟩ := LStore.intern_spec ⟨rkl, hlw⟩ hv hcap
  obtain ⟨rkl', hlw'⟩ := hlwf'
  have hns : (st.ls.intern w).1.ns = st.ns := LStore.ns_intern st.ls w
  have hlsw' : LsWF { st.lss with ls := (st.ls.intern w).1 } :=
    LsStore.wf_of_ls hlsw ⟨rkl', hlw'⟩ (LStore.scratchOn_intern st.ls w)
      (fun _ _ hu => LStore.view_intern_mono st.ls w hu)
      (fun _ _ hu => LStore.derived_intern hlw w hu)
  have hewf :
      EWFAt { st with lss := { st.lss with ls := (st.ls.intern w).1 } } rk :=
    EStore.wf_of_lss h hlsw' rfl
      (fun _ _ hu => by rw [hns]; exact hu)
      (fun _ _ hu => LStore.view_intern_mono st.ls w hu)
      (fun _ _ hu => hu)
      (fun _ _ _ => by rw [hns])
      (fun _ _ hu => LStore.derived_intern hlw w hu)
      (fun _ _ _ => rfl)
  rw [EStore.internLevel_eq]
  exact ⟨⟨rk, hewf⟩, EStore.internLevel_ext st w, rfl, rfl, rfl, hlview,
    denoteL_unfold hlw' hlview⟩

/-- con-leche: none — the same for a universe-argument LIST node. -/
theorem EStore.internLevels_spec {st : EStore} {w : LsNodeView}
    (h : StoreWF st) (hv : st.lss.ViewOK w) (hcap : st.lss.capOK w) :
    StoreWF (st.internLevels w).1 ∧ Ext st (st.internLevels w).1 ∧
      (st.internLevels w).1.pers = st.pers ∧
      (st.internLevels w).1.scr = st.scr ∧
      (st.internLevels w).1.scratchOn = st.scratchOn ∧
      (st.internLevels w).1.lss.view (st.internLevels w).2 = some w ∧
      denoteLs (st.internLevels w).1.lss (st.internLevels w).2 =
        denoteLsView (st.internLevels w).1.lss w := by
  obtain ⟨rk, h⟩ := h
  have hlsw : LsWF st.lss := h.lss
  obtain ⟨hlswf', -, hlsview⟩ := LsStore.intern_spec hlsw hv hcap
  have hls : (st.lss.intern w).1.ls = st.ls := LsStore.ls_intern st.lss w
  have hlsn : (st.lss.intern w).1.ls.ns = st.ns := congrArg LStore.ns hls
  have hewf : EWFAt { st with lss := (st.lss.intern w).1 } rk :=
    EStore.wf_of_lss h hlswf' (LsStore.scratchOn_intern st.lss w)
      (fun _ _ hu => by rw [hlsn]; exact hu)
      (fun _ _ hu => by rw [hls]; exact hu)
      (fun _ _ hu => LsStore.view_intern_mono st.lss w hu)
      (fun _ _ _ => by rw [hlsn])
      (fun _ _ _ => by rw [hls])
      (fun _ _ hu => LsStore.derived_intern hlsw w hu)
  rw [EStore.internLevels_eq]
  exact ⟨⟨rk, hewf⟩, EStore.internLevels_ext st w, rfl, rfl, rfl, hlsview,
    denoteLs_unfold hlsview⟩

#print axioms EStore.internName_spec
#print axioms EStore.internLevel_spec
#print axioms EStore.internLevels_spec

end ConRon.Bridge
