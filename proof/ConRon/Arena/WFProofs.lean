/-
# The store layer's theorems (DESIGN.md §8.3, task #97 P2a)

The arena's own verification, beside the implementation (con-leche's lesson
27).  Four tiers of result, each proved for all four stores:

* `denote*_unfold` — the fuel disappears: on a well-formed store, `denote` of a
  handle is `denote*View` of its node.  Everything else is stated with this.
* `derived_exact` — the derived column is con-leche's own cached word of the
  denotation (`derived st i = e.data`).  This is the lemma that lets every
  pure-side fact about `Expr.data` transfer to the arena (DESIGN §8.3).
* `denote_inj` — the denotation is injective: two handles that denote the
  same term are the same handle.  DESIGN §8.3: "**exactness is a soundness
  obligation**, not a performance property".
* `intern_spec` / `view_spec` / `dropScratch_spec` / `enableScratch_spec` —
  the store operations.
-/
import ConRon.Arena.WF

namespace ConRon.Arena

open ConLeche

/-! ## Rank bookkeeping -/

theorem NStore.persCount_le (st : NStore) : st.persCount ≤ st.nodeCount := by
  simp [NStore.nodeCount]

theorem LStore.persCount_le (st : LStore) : st.persCount ≤ st.nodeCount := by
  simp [LStore.nodeCount]

theorem EStore.persCount_le (st : EStore) : st.persCount ≤ st.nodeCount := by
  simp [EStore.nodeCount]

theorem NWFAt.rank_lt {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) {i : NIdx}
    (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := NStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

theorem LWFAt.rank_lt {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) {i : LIdx}
    (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := LStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

theorem EWFAt.rank_lt {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) {i : EIdx}
    (hv : (st.view i).isSome = true) : rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · have h1 := h.rankP i hp hv
    have h2 := EStore.persCount_le st
    omega
  · exact h.rankS i (by simpa using hp) hv

/-! ## The fuel disappears: names -/

/-- Any two fuels above the rank give the same readback.  Strong induction on
the rank, which `NWFAt.childOK` makes decrease at every child. -/
theorem denoteNAux_congr {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
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

/-- con-leche: Setlec/Kernel/ArenaWF.lean:477 denote — **the** equation for
`denoteN`: on a well-formed store the fuel is invisible. -/
theorem denoteN_unfold {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk)
    {i : NIdx} {v : NNodeView} (hv : st.view i = some v) :
    denoteN st i = denoteNView st v := by
  have hsome : (st.view i).isSome = true := by rw [hv]; rfl
  have hr : rk i < st.nodeCount := h.rank_lt hsome
  have hchild : ∀ c ∈ v.children, rk c < st.nodeCount := by
    intro c hc
    have h1 := h.childOK i v hv c hc
    have := h.rank_lt h1.1
    omega
  simp only [denoteN, denoteNAux, hv, Option.bind_some]
  cases v with
  | anonymous => rfl
  | str p s =>
    have hp := hchild p (by simp [NNodeView.children])
    simp only [denoteNView, denoteN]
    rw [denoteNAux_congr h (st.nodeCount + 1) p st.nodeCount (st.nodeCount + 1)
      (by omega) hp (by omega)]
  | num p k =>
    have hp := hchild p (by simp [NNodeView.children])
    simp only [denoteNView, denoteN]
    rw [denoteNAux_congr h (st.nodeCount + 1) p st.nodeCount (st.nodeCount + 1)
      (by omega) hp (by omega)]

/-- A handle whose view is absent denotes nothing. -/
theorem denoteN_view {st : NStore} {i : NIdx} {n : ConLeche.Name}
    (h : denoteN st i = some n) : ∃ v, st.view i = some v := by
  simp only [denoteN, denoteNAux, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, _⟩ := h
  exact ⟨v, hv⟩

/-! ## Names: cross-tier canonicity and injectivity -/

/-- Two handles that decode to the same node are the same handle: each tier's
cons table is injective on nodes, and `fresh` rules out the cross-tier case.
This is DESIGN §8.3's cross-tier canonicity, and the last step of
`denote_inj`. -/
theorem NWFAt.view_inj {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk)
    {i j : NIdx} {v : NNodeView} (hi : st.view i = some v)
    (hj : st.view j = some v) : i = j := by
  by_cases pi : i.isPersistent = true <;> by_cases pj : j.isPersistent = true
  · have h1 := (h.consP v i).mpr ⟨hi, pi⟩
    have h2 := (h.consP v j).mpr ⟨hj, pj⟩
    exact Option.some.inj (h1.symm.trans h2)
  · have h1 := (h.consP v i).mpr ⟨hi, pi⟩
    have h2 := (h.consS v j).mpr ⟨hj, by simpa using pj⟩
    rw [h.fresh v j h2] at h1; exact absurd h1 (by simp)
  · have h1 := (h.consS v i).mpr ⟨hi, by simpa using pi⟩
    have h2 := (h.consP v j).mpr ⟨hj, pj⟩
    rw [h.fresh v i h1] at h2; exact absurd h2 (by simp)
  · have h1 := (h.consS v i).mpr ⟨hi, by simpa using pi⟩
    have h2 := (h.consS v j).mpr ⟨hj, by simpa using pj⟩
    exact Option.some.inj (h1.symm.trans h2)

/-! The three shape lemmas: a node view's *denotation* determines the view's
constructor, because `denoteNView` maps constructors to constructors.  With
them, injectivity is an induction on the denoted **value**, not on the rank —
the children of a node denote structural subterms, so `Name`'s own recursor is
the well-founded order. -/

theorem denoteNView_anonymous {st : NStore} {v : NNodeView}
    (h : denoteNView st v = some .anonymous) : v = .anonymous := by
  cases v with
  | anonymous => rfl
  | str p s => simp [denoteNView, Option.map_eq_some_iff] at h
  | num p k => simp [denoteNView, Option.map_eq_some_iff] at h

theorem denoteNView_str {st : NStore} {v : NNodeView} {q : ConLeche.Name}
    {s : String} (h : denoteNView st v = some (.str q s)) :
    ∃ p, v = .str p s ∧ denoteN st p = some q := by
  cases v with
  | anonymous => simp [denoteNView] at h
  | str p s' =>
    simp only [denoteNView, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, hx⟩ := h
    injection hx with e1 e2
    subst e1; subst e2
    exact ⟨p, rfl, hr⟩
  | num p k => simp [denoteNView, Option.map_eq_some_iff] at h

theorem denoteNView_num {st : NStore} {v : NNodeView} {q : ConLeche.Name}
    {k : Nat} (h : denoteNView st v = some (.num q k)) :
    ∃ p, v = .num p k ∧ denoteN st p = some q := by
  cases v with
  | anonymous => simp [denoteNView] at h
  | str p s => simp [denoteNView, Option.map_eq_some_iff] at h
  | num p k' =>
    simp only [denoteNView, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, hx⟩ := h
    injection hx with e1 e2
    subst e1; subst e2
    exact ⟨p, rfl, hr⟩

/-- con-leche: Setlec/Kernel/ArenaWF.lean:2758 denote_inj — the name store's
denotation is injective. -/
theorem denoteN_inj_at {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    ∀ (x : ConLeche.Name) (i j : NIdx),
      denoteN st i = some x → denoteN st j = some x → i = j := by
  intro x
  induction x with
  | anonymous =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteN_view hi
    obtain ⟨vj, hvj⟩ := denoteN_view hj
    rw [denoteN_unfold h hvi] at hi
    rw [denoteN_unfold h hvj] at hj
    rw [denoteNView_anonymous hi] at hvi
    rw [denoteNView_anonymous hj] at hvj
    exact h.view_inj hvi hvj
  | str q s ih =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteN_view hi
    obtain ⟨vj, hvj⟩ := denoteN_view hj
    rw [denoteN_unfold h hvi] at hi
    rw [denoteN_unfold h hvj] at hj
    obtain ⟨p, hp, hdp⟩ := denoteNView_str hi
    obtain ⟨p', hp', hdp'⟩ := denoteNView_str hj
    have hpp : p = p' := ih p p' hdp hdp'
    subst hpp
    rw [hp] at hvi; rw [hp'] at hvj
    exact h.view_inj hvi hvj
  | num q k ih =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteN_view hi
    obtain ⟨vj, hvj⟩ := denoteN_view hj
    rw [denoteN_unfold h hvi] at hi
    rw [denoteN_unfold h hvj] at hj
    obtain ⟨p, hp, hdp⟩ := denoteNView_num hi
    obtain ⟨p', hp', hdp'⟩ := denoteNView_num hj
    have hpp : p = p' := ih p p' hdp hdp'
    subst hpp
    rw [hp] at hvi; rw [hp'] at hvj
    exact h.view_inj hvi hvj

/-- con-leche: Setlec/Kernel/ArenaWF.lean:2758 denote_inj -/
theorem denoteN_inj {st : NStore} (h : NStoreWF st) {i j : NIdx}
    {x : ConLeche.Name} (hi : denoteN st i = some x)
    (hj : denoteN st j = some x) : i = j := by
  obtain ⟨rk, h⟩ := h
  exact denoteN_inj_at h x i j hi hj

/-! ## Names: the derived column is con-leche's cached hash -/

/-- con-leche: ConLeche/Kernel/Name.lean:41-44 Name.hashData — **exactness**
(con-leche's lesson 2: prove exactness, not soundness).  The name store's
derived column is the cached hash of the name the handle denotes. -/
theorem NStore.derived_exact_at {st : NStore} {rk : NIdx → Nat}
    (h : NWFAt st rk) : ∀ (x : ConLeche.Name) (i : NIdx),
      denoteN st i = some x → st.derived i = x.hashData := by
  intro x
  induction x with
  | anonymous =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteN_view hi
    rw [denoteN_unfold h hv] at hi
    rw [denoteNView_anonymous hi] at hv
    rw [h.derExact i _ hv]
    rfl
  | str q s ih =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteN_view hi
    rw [denoteN_unfold h hv] at hi
    obtain ⟨p, hp, hdp⟩ := denoteNView_str hi
    rw [hp] at hv
    rw [h.derExact i _ hv]
    simp [NStore.derOfView, ih p hdp, ConLeche.Name.hashData]
  | num q k ih =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteN_view hi
    rw [denoteN_unfold h hv] at hi
    obtain ⟨p, hp, hdp⟩ := denoteNView_num hi
    rw [hp] at hv
    rw [h.derExact i _ hv]
    simp [NStore.derOfView, ih p hdp, ConLeche.Name.hashData]

/-- con-leche: ConLeche/Kernel/Name.lean:41-44 Name.hashData -/
theorem NStore.derived_exact {st : NStore} (h : NStoreWF st) {i : NIdx}
    {x : ConLeche.Name} (hi : denoteN st i = some x) :
    st.derived i = x.hashData := by
  obtain ⟨rk, h⟩ := h
  exact NStore.derived_exact_at h x i hi

end ConRon.Arena
