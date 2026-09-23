/-
# `ConRon.Bridge.Promote.Weak` — the readback at the promote window's invariant

`Arena/WF.lean`'s `StoreWF'` (task #97-P5-Fresh) is the invariant a store has
while a promotion is in flight: `StoreWF` minus the freshness clauses at every
tier, and minus `consS`'s `←` half and `bmKeyS`'s strength.  None of the four
missing clauses is about the RANK, and the rank is all the readback needs: a
node's children rank below it, so the fuel `denote*` is run at is invisible.

So this module is `Arena/WFProofs.lean`'s "the fuel disappears" layer and its
`dropScratch` layer, re-run from the weak invariant — the argument verbatim,
one word changed per lemma.  It is what the promotion's exactness
(`Bridge/Promote/Exact.lean`) unfolds `denote*` with, and what carries a
persistent denotation across the bracket's closing `dropScratch`
(`PExt.dropScratch'`), which task #97-P3-Checker's `Fold.lean` note names as
the second of `checkDeclStep_bridge`'s three blockers.

Every name here is primed and lives in `ConRon.Bridge`: the strong lemmas are
`ConRon.Arena.*`, and `Refine2/Checker/Shape.lean` has its own
`ConRon.Arena.EWFAt'.rank_lt`, so a `ConRon.Arena`-namespaced copy here would
clash in any environment importing both tiers (the capstone's).
-/
import ConRon.Bridge.Promote.Pers

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## Rank bookkeeping -/

theorem rankN_lt' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk) {i : NIdx}
    (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := NStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

theorem rankL_lt' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk) {i : LIdx}
    (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := LStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

theorem rankE_lt' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) {i : EIdx}
    (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := EStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

/-! ## The fuel disappears: names -/

theorem denoteNAux_congr' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk) :
    ∀ (n : Nat) (i : NIdx) (f f' : Nat), rk i < n → rk i < f → rk i < f' →
      denoteNAux st f i = denoteNAux st f' i := by
  intro n
  induction n with
  | zero => intro i f f' hn; omega
  | succ m ih =>
    intro i f f' hn hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [denoteNAux]
    cases hv : st.view i with
    | none => simp
    | some v =>
      have hchild : ∀ c ∈ v.children, rk c < m ∧ rk c < g ∧ rk c < g' := by
        intro c hc
        have := h.childOK i v hv c hc
        omega
      cases v with
      | anonymous => simp
      | str p s =>
        have := hchild p (by simp [NNodeView.children])
        simp only [Option.bind_some, ih p g g' this.1 this.2.1 this.2.2]
      | num p k =>
        have := hchild p (by simp [NNodeView.children])
        simp only [Option.bind_some, ih p g g' this.1 this.2.1 this.2.2]

/-- con-leche: none — arena infrastructure; `denoteN_unfold` at the promote
window's invariant. -/
theorem denoteN_unfold' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk)
    {i : NIdx} {v : NNodeView} (hv : st.view i = some v) :
    denoteN st i = denoteNView st v := by
  have hchild : ∀ c ∈ v.children, rk c < st.nodeCount := by
    intro c hc
    have h1 := h.childOK i v hv c hc
    have := rankN_lt' h h1.1
    omega
  simp only [denoteN, denoteNAux, hv, Option.bind_some]
  cases v with
  | anonymous => rfl
  | str p s =>
    have hp := hchild p (by simp [NNodeView.children])
    simp only [denoteNView, denoteN]
    rw [denoteNAux_congr' h (st.nodeCount + 1) p st.nodeCount (st.nodeCount + 1)
      (by omega) hp (by omega)]
  | num p k =>
    have hp := hchild p (by simp [NNodeView.children])
    simp only [denoteNView, denoteN]
    rw [denoteNAux_congr' h (st.nodeCount + 1) p st.nodeCount (st.nodeCount + 1)
      (by omega) hp (by omega)]

/-! ## The fuel disappears: levels -/

theorem denoteLAux_congr' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk) :
    ∀ (n : Nat) (i : LIdx) (f f' : Nat), rk i < n → rk i < f → rk i < f' →
      denoteLAux st f i = denoteLAux st f' i := by
  intro n
  induction n with
  | zero => intro i f f' hn; omega
  | succ m ih =>
    intro i f f' hn hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [denoteLAux]
    cases hv : st.view i with
    | none => simp
    | some v =>
      have hchild : ∀ c ∈ v.lchildren, rk c < m ∧ rk c < g ∧ rk c < g' := by
        intro c hc
        have := h.childOK i v hv c hc
        omega
      cases v with
      | zero => simp
      | succ u =>
        have := hchild u (by simp [LNodeView.lchildren])
        simp only [Option.bind_some, ih u g g' this.1 this.2.1 this.2.2]
      | max u w =>
        have h1 := hchild u (by simp [LNodeView.lchildren])
        have h2 := hchild w (by simp [LNodeView.lchildren])
        simp only [Option.bind_some, ih u g g' h1.1 h1.2.1 h1.2.2,
          ih w g g' h2.1 h2.2.1 h2.2.2]
      | imax u w =>
        have h1 := hchild u (by simp [LNodeView.lchildren])
        have h2 := hchild w (by simp [LNodeView.lchildren])
        simp only [Option.bind_some, ih u g g' h1.1 h1.2.1 h1.2.2,
          ih w g g' h2.1 h2.2.1 h2.2.2]
      | param n => simp

/-- con-leche: none — arena infrastructure; `denoteL_unfold` at the promote
window's invariant. -/
theorem denoteL_unfold' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk)
    {i : LIdx} {v : LNodeView} (hv : st.view i = some v) :
    denoteL st i = denoteLView st v := by
  have hchild : ∀ c ∈ v.lchildren, rk c < st.nodeCount := by
    intro c hc
    have h1 := h.childOK i v hv c hc
    have := rankL_lt' h h1.1
    omega
  simp only [denoteL, denoteLAux, hv, Option.bind_some]
  cases v with
  | zero => rfl
  | succ u =>
    have hu := hchild u (by simp [LNodeView.lchildren])
    simp only [denoteLView, denoteL]
    rw [denoteLAux_congr' h (st.nodeCount + 1) u st.nodeCount (st.nodeCount + 1)
      (by omega) hu (by omega)]
  | max u w =>
    have hu := hchild u (by simp [LNodeView.lchildren])
    have hw := hchild w (by simp [LNodeView.lchildren])
    simp only [denoteLView, denoteL]
    rw [denoteLAux_congr' h (st.nodeCount + 1) u st.nodeCount (st.nodeCount + 1)
      (by omega) hu (by omega),
      denoteLAux_congr' h (st.nodeCount + 1) w st.nodeCount (st.nodeCount + 1)
      (by omega) hw (by omega)]
  | imax u w =>
    have hu := hchild u (by simp [LNodeView.lchildren])
    have hw := hchild w (by simp [LNodeView.lchildren])
    simp only [denoteLView, denoteL]
    rw [denoteLAux_congr' h (st.nodeCount + 1) u st.nodeCount (st.nodeCount + 1)
      (by omega) hu (by omega),
      denoteLAux_congr' h (st.nodeCount + 1) w st.nodeCount (st.nodeCount + 1)
      (by omega) hw (by omega)]
  | param n => rfl

/-! ## The fuel disappears: expressions -/

theorem denoteEAux_congr' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    ∀ (n : Nat) (i : EIdx) (f f' : Nat), rk i < n → rk i < f → rk i < f' →
      denoteEAux st f i = denoteEAux st f' i := by
  intro n
  induction n with
  | zero => intro i f f' hn; omega
  | succ m ih =>
    intro i f f' hn hf hf'
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', f' = g' + 1 := ⟨f' - 1, by omega⟩
    simp only [denoteEAux]
    cases hv : st.view i with
    | none => simp
    | some v =>
      have hchild : ∀ c ∈ v.echildren, rk c < m ∧ rk c < g ∧ rk c < g' := by
        intro c hc
        have := h.childOK i v hv c hc
        omega
      cases v with
      | bvar _ => simp
      | sort _ => simp
      | const _ _ => simp
      | lit _ => simp
      | fvar j ty =>
        have h1 := hchild ty (by simp [ENodeView.echildren])
        simp only [Option.bind_some, ih ty g g' h1.1 h1.2.1 h1.2.2]
      | proj n j e =>
        have h1 := hchild e (by simp [ENodeView.echildren])
        simp only [Option.bind_some, ih e g g' h1.1 h1.2.1 h1.2.2]
      | app a b =>
        have h1 := hchild a (by simp [ENodeView.echildren])
        have h2 := hchild b (by simp [ENodeView.echildren])
        simp only [Option.bind_some, ih a g g' h1.1 h1.2.1 h1.2.2,
          ih b g g' h2.1 h2.2.1 h2.2.2]
      | lam ty b m =>
        have h1 := hchild ty (by simp [ENodeView.echildren])
        have h2 := hchild b (by simp [ENodeView.echildren])
        simp only [Option.bind_some, ih ty g g' h1.1 h1.2.1 h1.2.2,
          ih b g g' h2.1 h2.2.1 h2.2.2]
      | forallE ty b m =>
        have h1 := hchild ty (by simp [ENodeView.echildren])
        have h2 := hchild b (by simp [ENodeView.echildren])
        simp only [Option.bind_some, ih ty g g' h1.1 h1.2.1 h1.2.2,
          ih b g g' h2.1 h2.2.1 h2.2.2]
      | letE ty w b =>
        have h1 := hchild ty (by simp [ENodeView.echildren])
        have h2 := hchild w (by simp [ENodeView.echildren])
        have h3 := hchild b (by simp [ENodeView.echildren])
        simp only [Option.bind_some, ih ty g g' h1.1 h1.2.1 h1.2.2,
          ih w g g' h2.1 h2.2.1 h2.2.2, ih b g g' h3.1 h3.2.1 h3.2.2]

/-- con-leche: none — arena infrastructure; **`denoteE_unfold` at the promote
window's invariant** — the one equation the promotion's exactness needs at
every node it builds. -/
theorem denoteE_unfold' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk)
    {i : EIdx} {v : ENodeView} (hv : st.view i = some v) :
    denoteE st i = denoteEView st v := by
  have hchild : ∀ c ∈ v.echildren, rk c < st.nodeCount := by
    intro c hc
    have h1 := h.childOK i v hv c hc
    have := rankE_lt' h h1.1
    omega
  have key : ∀ c ∈ v.echildren,
      denoteEAux st st.nodeCount c = denoteEAux st (st.nodeCount + 1) c := by
    intro c hc
    exact denoteEAux_congr' h (st.nodeCount + 1) c st.nodeCount (st.nodeCount + 1)
      (by have := hchild c hc; omega) (hchild c hc) (by have := hchild c hc; omega)
  simp only [denoteE, denoteEAux, hv, Option.bind_some]
  cases v with
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | fvar j ty =>
    simp only [denoteEView, denoteE]
    rw [key ty (by simp [ENodeView.echildren])]
  | proj n j e =>
    simp only [denoteEView, denoteE]
    rw [key e (by simp [ENodeView.echildren])]
  | app a b =>
    simp only [denoteEView, denoteE]
    rw [key a (by simp [ENodeView.echildren]), key b (by simp [ENodeView.echildren])]
  | lam ty b m =>
    simp only [denoteEView, denoteE]
    rw [key ty (by simp [ENodeView.echildren]), key b (by simp [ENodeView.echildren])]
  | forallE ty b m =>
    simp only [denoteEView, denoteE]
    rw [key ty (by simp [ENodeView.echildren]), key b (by simp [ENodeView.echildren])]
  | letE ty w b =>
    simp only [denoteEView, denoteE]
    rw [key ty (by simp [ENodeView.echildren]), key w (by simp [ENodeView.echildren]),
      key b (by simp [ENodeView.echildren])]

/-! ## The bracket's closing `dropScratch`, from the weak invariant

`Arena/WFProofs.lean`'s `denote*_dropScratch` family, one word changed per
lemma: the recursion never leaves the persistent tier, because a persistent
node's children are persistent (`childOK`, which the weak invariant keeps),
and the strong invariant on the far side of the drop is
`StoreWF'.dropScratch_wf`'s. -/

theorem denoteNAux_dropScratch' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk) :
    ∀ (f : Nat) (i : NIdx) (x : ConLeche.Name), i.isPersistent = true →
      denoteNAux st f i = some x → denoteNAux st.dropScratch f i = some x := by
  intro f
  induction f with
  | zero => intro i x _ hd; simp [denoteNAux] at hd
  | succ k ih =>
    intro i x hp hd
    simp only [denoteNAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hv, hd⟩ := hd
    refine ⟨v, by rw [NStore.view_dropScratch_pers st hp]; exact hv, ?_⟩
    cases v with
    | anonymous => exact hd
    | str p s =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih p q ((h.childOK i _ hv p (by simp [NNodeView.children])).2.2 hp) hq, he⟩
    | num p n =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih p q ((h.childOK i _ hv p (by simp [NNodeView.children])).2.2 hp) hq, he⟩

theorem denoteN_dropScratch_pers' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk)
    {i : NIdx} {x : ConLeche.Name} (hp : i.isPersistent = true)
    (hd : denoteN st i = some x) : denoteN st.dropScratch i = some x := by
  have h' := NStore.dropScratch_wfAt' h
  obtain ⟨v, hv⟩ := denoteN_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [NStore.view_dropScratch_pers st hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := rankN_lt' h (by rw [hv]; rfl)
  have h1 : denoteNAux st.dropScratch (st.nodeCount + 1) i = some x :=
    denoteNAux_dropScratch' h _ i x hp hd
  rw [denoteN, denoteNAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

theorem denoteLAux_dropScratch' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk) :
    ∀ (f : Nat) (i : LIdx) (x : Level), i.isPersistent = true →
      denoteLAux st f i = some x → denoteLAux st.dropScratch f i = some x := by
  obtain ⟨rkn, hn⟩ := h.ns
  intro f
  induction f with
  | zero => intro i x _ hd; simp [denoteLAux] at hd
  | succ k ih =>
    intro i x hp hd
    simp only [denoteLAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hv, hd⟩ := hd
    refine ⟨v, by rw [LStore.view_dropScratch_pers st hp]; exact hv, ?_⟩
    cases v with
    | zero => exact hd
    | succ u =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih u q ((h.childOK i _ hv u (by simp [LNodeView.lchildren])).2.2 hp) hq, he⟩
    | max u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ((h.childOK i _ hv u (by simp [LNodeView.lchildren])).2.2 hp) ha,
        ih w b ((h.childOK i _ hv w (by simp [LNodeView.lchildren])).2.2 hp) hb, he⟩
    | imax u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ((h.childOK i _ hv u (by simp [LNodeView.lchildren])).2.2 hp) ha,
        ih w b ((h.childOK i _ hv w (by simp [LNodeView.lchildren])).2.2 hp) hb, he⟩
    | param n =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      refine ⟨q, ?_, he⟩
      exact denoteN_dropScratch_pers' hn
        ((h.nchildOK i _ hv n (by simp [LNodeView.nchildren])).2 hp) hq

theorem denoteL_dropScratch_pers' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk)
    {i : LIdx} {x : Level} (hp : i.isPersistent = true)
    (hd : denoteL st i = some x) : denoteL st.dropScratch i = some x := by
  have h' := LStore.dropScratch_wfAt' h
  obtain ⟨v, hv⟩ := denoteL_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [LStore.view_dropScratch_pers st hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := rankL_lt' h (by rw [hv]; rfl)
  have h1 : denoteLAux st.dropScratch (st.nodeCount + 1) i = some x :=
    denoteLAux_dropScratch' h _ i x hp hd
  rw [denoteL, denoteLAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

theorem denoteLList_dropScratch' {ls : LStore} {rk : LIdx → Nat} (h : LWFAt' ls rk) :
    ∀ (us : List LIdx) (xs : List Level), (∀ c ∈ us, c.isPersistent = true) →
      denoteLList ls us = some xs → denoteLList ls.dropScratch us = some xs := by
  intro us
  induction us with
  | nil => intro xs _ hd; exact hd
  | cons u rest ih =>
    intro xs hp hd
    simp only [denoteLList, opt2_eq_some_iff] at hd ⊢
    obtain ⟨a, b, ha, hb, he⟩ := hd
    exact ⟨a, b, denoteL_dropScratch_pers' h (hp u (by simp)) ha,
      ih b (fun c hc => hp c (by simp [hc])) hb, he⟩

theorem denoteLs_dropScratch_pers' {st : LsStore} (h : LsWF' st) {i : LsIdx}
    {xs : List Level} (hp : i.isPersistent = true) (hd : denoteLs st i = some xs) :
    denoteLs st.dropScratch i = some xs := by
  obtain ⟨rkl, hl⟩ := h.ls
  obtain ⟨us, hus, hlist⟩ := denoteLs_view hd
  rw [denoteLs, LsStore.view_dropScratch_pers st hp, hus]
  exact denoteLList_dropScratch' hl us xs
    (fun c hc => (h.lchildOK i us hus c hc).2 hp) hlist

theorem denoteEAux_dropScratch' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    ∀ (f : Nat) (i : EIdx) (x : Expr), i.isPersistent = true →
      denoteEAux st f i = some x → denoteEAux st.dropScratch f i = some x := by
  have hlsw : LsWF' st.lss := h.lss
  obtain ⟨rkl, hl⟩ : LStoreWF' st.ls := hlsw.ls
  obtain ⟨rkn, hn⟩ : NStoreWF' st.ns := hl.ns
  have hbm : ∀ i, i.isPersistent = true →
      ∀ ty b mi, st.viewBindI i = some (ty, b, mi) → mi.isPersistent = true :=
    fun i hp ty b mi hh => (h.bmChildOK i ty b mi hh).2.1 hp
  intro f
  induction f with
  | zero => intro i x _ hd; simp [denoteEAux] at hd
  | succ k ih =>
    intro i x hp hd
    simp only [denoteEAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hv, hd⟩ := hd
    refine ⟨v, by rw [EStore.view_dropScratch_pers st (hbm i hp) hp]; exact hv, ?_⟩
    cases v with
    | bvar _ => exact hd
    | lit _ => exact hd
    | fvar j ty =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih ty q ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hq, he⟩
    | sort u =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      refine ⟨q, ?_, he⟩
      exact denoteL_dropScratch_pers' hl
        ((h.lchildOK i _ hv u (by simp [ENodeView.lchildren])).2 hp) hq
    | const n us =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      refine ⟨a, b, ?_, ?_, he⟩
      · exact denoteN_dropScratch_pers' hn
          ((h.nchildOK i _ hv n (by simp [ENodeView.nchildren])).2 hp) ha
      · exact denoteLs_dropScratch_pers' hlsw
          ((h.lschildOK i _ hv us (by simp [ENodeView.lschildren])).2 hp) hb
    | app g a =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih g p ((h.childOK i _ hv g (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih a q ((h.childOK i _ hv a (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | lam ty b m =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih ty p ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih b q ((h.childOK i _ hv b (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | forallE ty b m =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih ty p ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih b q ((h.childOK i _ hv b (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | letE ty val b =>
      simp only [opt3_eq_some_iff] at hd ⊢
      obtain ⟨p, q, r, hp1, hq1, hr1, he⟩ := hd
      exact ⟨p, q, r,
        ih ty p ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih val q ((h.childOK i _ hv val (by simp [ENodeView.echildren])).2.2 hp) hq1,
        ih b r ((h.childOK i _ hv b (by simp [ENodeView.echildren])).2.2 hp) hr1, he⟩
    | proj n j e =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      refine ⟨p, q, ?_, ih e q ((h.childOK i _ hv e (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
      exact denoteN_dropScratch_pers' hn
        ((h.nchildOK i _ hv n (by simp [ENodeView.nchildren])).2 hp) hp1

/-- con-leche: none — arena infrastructure; `EStore.dropScratch_denote_pers`
from the promote window's invariant. -/
theorem denoteE_dropScratch_pers' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk)
    {i : EIdx} {e : Expr} (hp : i.isPersistent = true)
    (hd : denoteE st i = some e) : denoteE st.dropScratch i = some e := by
  have h' := EStore.dropScratch_wfAt' h
  obtain ⟨v, hv⟩ := denoteE_view hd
  have hbm : ∀ ty b mi, st.viewBindI i = some (ty, b, mi) → mi.isPersistent = true :=
    fun ty b mi hh => (h.bmChildOK i ty b mi hh).2.1 hp
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [EStore.view_dropScratch_pers st hbm hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := rankE_lt' h (by rw [hv]; rfl)
  have h1 : denoteEAux st.dropScratch (st.nodeCount + 1) i = some e :=
    denoteEAux_dropScratch' h _ i e hp hd
  rw [denoteE, denoteEAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

/-- con-leche: none — arena infrastructure; **the bracket's closing step
carries every persistent denotation**, from the promote window's invariant.
`PExt.dropScratch` with `StoreWF` weakened to `StoreWF'`: the one form of it
the promotion bracket can use, because the promotion leaves only `StoreWF'`
behind (task #97-P5-Fresh). -/
theorem PExt.dropScratch' {st : EStore} (h : StoreWF' st) :
    PExt st st.dropScratch := by
  obtain ⟨rk, hwa⟩ := h
  have hlss : LsWF' st.lss := hwa.lss
  obtain ⟨rkl, hl⟩ : LStoreWF' st.lss.ls := hlss.ls
  obtain ⟨rkn, hn⟩ : NStoreWF' st.lss.ls.ns := hl.ns
  exact ⟨⟨⟨fun i n hp hd => denoteN_dropScratch_pers' hn hp hd,
      fun i u hp hd => denoteL_dropScratch_pers' hl hp hd⟩,
    fun i us hp hd => denoteLs_dropScratch_pers' hlss hp hd⟩,
    fun i e hp hd => denoteE_dropScratch_pers' hwa hp hd⟩

end ConRon.Bridge
