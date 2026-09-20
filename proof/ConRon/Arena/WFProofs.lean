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

/-! ## con-leche's `Hashable` instances are the cached fields

`instance : Hashable Name := ⟨Name.hashData⟩` (`Kernel/Name.lean:49`) and the
same for `Level` (`Kernel/Expr.lean:58`), so `hash n` in `Expr.data`'s
formulas *is* the store's derived column. -/

@[simp] theorem hash_name_eq (n : ConLeche.Name) : hash n = n.hashData := rfl
@[simp] theorem hash_level_eq (u : Level) : hash u = u.hashData := rfl

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

/-! ## The fuel disappears: levels -/

theorem denoteLAux_congr {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
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

/-- con-leche: Setlec/Kernel/ArenaWF.lean:477 denote -/
theorem denoteL_unfold {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk)
    {i : LIdx} {v : LNodeView} (hv : st.view i = some v) :
    denoteL st i = denoteLView st v := by
  have hsome : (st.view i).isSome = true := by rw [hv]; rfl
  have hchild : ∀ c ∈ v.lchildren, rk c < st.nodeCount := by
    intro c hc
    have h1 := h.childOK i v hv c hc
    have := h.rank_lt h1.1
    omega
  simp only [denoteL, denoteLAux, hv, Option.bind_some]
  cases v with
  | zero => rfl
  | succ u =>
    have hu := hchild u (by simp [LNodeView.lchildren])
    simp only [denoteLView, denoteL]
    rw [denoteLAux_congr h (st.nodeCount + 1) u st.nodeCount (st.nodeCount + 1)
      (by omega) hu (by omega)]
  | max u w =>
    have hu := hchild u (by simp [LNodeView.lchildren])
    have hw := hchild w (by simp [LNodeView.lchildren])
    simp only [denoteLView, denoteL]
    rw [denoteLAux_congr h (st.nodeCount + 1) u st.nodeCount (st.nodeCount + 1)
      (by omega) hu (by omega),
      denoteLAux_congr h (st.nodeCount + 1) w st.nodeCount (st.nodeCount + 1)
      (by omega) hw (by omega)]
  | imax u w =>
    have hu := hchild u (by simp [LNodeView.lchildren])
    have hw := hchild w (by simp [LNodeView.lchildren])
    simp only [denoteLView, denoteL]
    rw [denoteLAux_congr h (st.nodeCount + 1) u st.nodeCount (st.nodeCount + 1)
      (by omega) hu (by omega),
      denoteLAux_congr h (st.nodeCount + 1) w st.nodeCount (st.nodeCount + 1)
      (by omega) hw (by omega)]
  | param n => rfl

theorem denoteL_view {st : LStore} {i : LIdx} {u : Level}
    (h : denoteL st i = some u) : ∃ v, st.view i = some v := by
  simp only [denoteL, denoteLAux, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, _⟩ := h
  exact ⟨v, hv⟩

theorem LWFAt.view_inj {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk)
    {i j : LIdx} {v : LNodeView} (hi : st.view i = some v)
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

theorem denoteLView_zero {st : LStore} {v : LNodeView}
    (h : denoteLView st v = some .zero) : v = .zero := by
  cases v <;> simp_all [denoteLView, Option.map_eq_some_iff]

theorem denoteLView_succ {st : LStore} {v : LNodeView} {a : Level}
    (h : denoteLView st v = some (.succ a)) :
    ∃ u, v = .succ u ∧ denoteL st u = some a := by
  cases v with
  | succ u =>
    simp only [denoteLView, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, hx⟩ := h
    injection hx with e1; subst e1
    exact ⟨u, rfl, hr⟩
  | _ => simp_all [denoteLView, Option.map_eq_some_iff]

theorem denoteLView_max {st : LStore} {v : LNodeView} {a b : Level}
    (h : denoteLView st v = some (.max a b)) :
    ∃ u w, v = .max u w ∧ denoteL st u = some a ∧ denoteL st w = some b := by
  cases v with
  | max u w =>
    simp only [denoteLView, opt2_eq_some_iff] at h
    obtain ⟨x, y, hx, hy, he⟩ := h
    injection he with e1 e2; subst e1; subst e2
    exact ⟨u, w, rfl, hx, hy⟩
  | _ => simp_all [denoteLView, Option.map_eq_some_iff]

theorem denoteLView_imax {st : LStore} {v : LNodeView} {a b : Level}
    (h : denoteLView st v = some (.imax a b)) :
    ∃ u w, v = .imax u w ∧ denoteL st u = some a ∧ denoteL st w = some b := by
  cases v with
  | imax u w =>
    simp only [denoteLView, opt2_eq_some_iff] at h
    obtain ⟨x, y, hx, hy, he⟩ := h
    injection he with e1 e2; subst e1; subst e2
    exact ⟨u, w, rfl, hx, hy⟩
  | _ => simp_all [denoteLView, Option.map_eq_some_iff]

theorem denoteLView_param {st : LStore} {v : LNodeView} {nm : ConLeche.Name}
    (h : denoteLView st v = some (.param nm)) :
    ∃ n, v = .param n ∧ denoteN st.ns n = some nm := by
  cases v with
  | param n =>
    simp only [denoteLView, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, hx⟩ := h
    injection hx with e1; subst e1
    exact ⟨n, rfl, hr⟩
  | _ => simp_all [denoteLView, Option.map_eq_some_iff]

/-- con-leche: Setlec/Kernel/ArenaWF.lean:2758 denote_inj — the level store's
denotation is injective. -/
theorem denoteL_inj_at {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    ∀ (x : Level) (i j : LIdx),
      denoteL st i = some x → denoteL st j = some x → i = j := by
  intro x
  induction x with
  | zero =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteL_view hi
    obtain ⟨vj, hvj⟩ := denoteL_view hj
    rw [denoteL_unfold h hvi] at hi
    rw [denoteL_unfold h hvj] at hj
    rw [denoteLView_zero hi] at hvi
    rw [denoteLView_zero hj] at hvj
    exact h.view_inj hvi hvj
  | succ a ih =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteL_view hi
    obtain ⟨vj, hvj⟩ := denoteL_view hj
    rw [denoteL_unfold h hvi] at hi
    rw [denoteL_unfold h hvj] at hj
    obtain ⟨u, hu, hdu⟩ := denoteLView_succ hi
    obtain ⟨u', hu', hdu'⟩ := denoteLView_succ hj
    have : u = u' := ih u u' hdu hdu'
    subst this
    rw [hu] at hvi; rw [hu'] at hvj
    exact h.view_inj hvi hvj
  | max a b ih1 ih2 =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteL_view hi
    obtain ⟨vj, hvj⟩ := denoteL_view hj
    rw [denoteL_unfold h hvi] at hi
    rw [denoteL_unfold h hvj] at hj
    obtain ⟨u, w, hu, hdu, hdw⟩ := denoteLView_max hi
    obtain ⟨u', w', hu', hdu', hdw'⟩ := denoteLView_max hj
    have e1 : u = u' := ih1 u u' hdu hdu'
    have e2 : w = w' := ih2 w w' hdw hdw'
    subst e1; subst e2
    rw [hu] at hvi; rw [hu'] at hvj
    exact h.view_inj hvi hvj
  | imax a b ih1 ih2 =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteL_view hi
    obtain ⟨vj, hvj⟩ := denoteL_view hj
    rw [denoteL_unfold h hvi] at hi
    rw [denoteL_unfold h hvj] at hj
    obtain ⟨u, w, hu, hdu, hdw⟩ := denoteLView_imax hi
    obtain ⟨u', w', hu', hdu', hdw'⟩ := denoteLView_imax hj
    have e1 : u = u' := ih1 u u' hdu hdu'
    have e2 : w = w' := ih2 w w' hdw hdw'
    subst e1; subst e2
    rw [hu] at hvi; rw [hu'] at hvj
    exact h.view_inj hvi hvj
  | param nm =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteL_view hi
    obtain ⟨vj, hvj⟩ := denoteL_view hj
    rw [denoteL_unfold h hvi] at hi
    rw [denoteL_unfold h hvj] at hj
    obtain ⟨n, hn, hdn⟩ := denoteLView_param hi
    obtain ⟨n', hn', hdn'⟩ := denoteLView_param hj
    have : n = n' := denoteN_inj h.ns hdn hdn'
    subst this
    rw [hn] at hvi; rw [hn'] at hvj
    exact h.view_inj hvi hvj

/-- con-leche: Setlec/Kernel/ArenaWF.lean:2758 denote_inj -/
theorem denoteL_inj {st : LStore} (h : LStoreWF st) {i j : LIdx} {x : Level}
    (hi : denoteL st i = some x) (hj : denoteL st j = some x) : i = j := by
  obtain ⟨rk, h⟩ := h
  exact denoteL_inj_at h x i j hi hj

/-- con-leche: ConLeche/Kernel/Expr.lean:47-53 Level.hashData and
ConLeche/Kernel/Expr.lean:118-122 levelHasParam — exactness of the level
store's derived column. -/
theorem LStore.derived_exact_at {st : LStore} {rk : LIdx → Nat}
    (h : LWFAt st rk) : ∀ (x : Level) (i : LIdx),
      denoteL st i = some x → st.derived i = ⟨x.hashData, levelHasParam x⟩ := by
  intro x
  induction x with
  | zero =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteL_view hi
    rw [denoteL_unfold h hv] at hi
    rw [denoteLView_zero hi] at hv
    rw [h.derExact i _ hv]
    rfl
  | succ a ih =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteL_view hi
    rw [denoteL_unfold h hv] at hi
    obtain ⟨u, hu, hdu⟩ := denoteLView_succ hi
    rw [hu] at hv
    rw [h.derExact i _ hv]
    simp [LStore.derOfView, ih u hdu, ConLeche.Level.hashData, levelHasParam]
  | max a b ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteL_view hi
    rw [denoteL_unfold h hv] at hi
    obtain ⟨u, w, hu, hdu, hdw⟩ := denoteLView_max hi
    rw [hu] at hv
    rw [h.derExact i _ hv]
    simp [LStore.derOfView, ih1 u hdu, ih2 w hdw, ConLeche.Level.hashData,
      levelHasParam]
  | imax a b ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteL_view hi
    rw [denoteL_unfold h hv] at hi
    obtain ⟨u, w, hu, hdu, hdw⟩ := denoteLView_imax hi
    rw [hu] at hv
    rw [h.derExact i _ hv]
    simp [LStore.derOfView, ih1 u hdu, ih2 w hdw, ConLeche.Level.hashData,
      levelHasParam]
  | param nm =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteL_view hi
    rw [denoteL_unfold h hv] at hi
    obtain ⟨n, hn, hdn⟩ := denoteLView_param hi
    rw [hn] at hv
    rw [h.derExact i _ hv]
    simp [LStore.derOfView, NStore.derived_exact h.ns hdn,
      ConLeche.Level.hashData, levelHasParam]

/-- con-leche: ConLeche/Kernel/Expr.lean:47-53 Level.hashData -/
theorem LStore.derived_exact {st : LStore} (h : LStoreWF st) {i : LIdx}
    {x : Level} (hi : denoteL st i = some x) :
    st.derived i = ⟨x.hashData, levelHasParam x⟩ := by
  obtain ⟨rk, h⟩ := h
  exact LStore.derived_exact_at h x i hi

/-! ## Level lists

A list node has no `LsIdx` child, so there is no rank, no fuel and no
`congr` lemma: `denoteLs` unfolds definitionally. -/

theorem denoteLs_view {st : LsStore} {i : LsIdx} {xs : List Level}
    (h : denoteLs st i = some xs) :
    ∃ us, st.view i = some us ∧ denoteLList st.ls us = some xs := by
  unfold denoteLs at h
  cases hv : st.view i with
  | none => rw [hv] at h; simp at h
  | some us => rw [hv] at h; exact ⟨us, rfl, h⟩

/-- con-leche: Setlec/Kernel/ArenaWF.lean:477 denote — the level-list store's
unfolding equation. -/
theorem denoteLs_unfold {st : LsStore} {i : LsIdx} {us : LsNodeView}
    (hv : st.view i = some us) : denoteLs st i = denoteLsView st us := by
  unfold denoteLs denoteLsView; rw [hv]

theorem LsWF.view_inj {st : LsStore} (h : LsWF st) {i j : LsIdx}
    {v : LsNodeView} (hi : st.view i = some v) (hj : st.view j = some v) :
    i = j := by
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

/-- Two handle lists that read back as the same level list are the same list:
`denoteL` is injective elementwise. -/
theorem denoteLList_inj {ls : LStore} (h : LStoreWF ls) :
    ∀ (us us' : List LIdx) (xs : List Level),
      denoteLList ls us = some xs → denoteLList ls us' = some xs → us = us' := by
  intro us
  induction us with
  | nil =>
    intro us' xs h1 h2
    simp only [denoteLList] at h1
    have hx : xs = [] := (Option.some.inj h1).symm
    subst hx
    cases us' with
    | nil => rfl
    | cons u r => simp [denoteLList] at h2
  | cons u r ih =>
    intro us' xs h1 h2
    simp only [denoteLList, opt2_eq_some_iff] at h1
    obtain ⟨a, as, ha, has, hxs⟩ := h1
    cases us' with
    | nil =>
      simp only [denoteLList] at h2
      rw [← hxs] at h2
      simp at h2
    | cons u' r' =>
      simp only [denoteLList, opt2_eq_some_iff] at h2
      obtain ⟨a', as', ha', has', hxs'⟩ := h2
      rw [← hxs] at hxs'
      injection hxs' with e1 e2
      subst e1; subst e2
      rw [denoteL_inj h ha ha', ih r' _ has has']

/-- con-leche: Setlec/Kernel/ArenaWF.lean:2758 denote_inj -/
theorem denoteLs_inj {st : LsStore} (h : LsStoreWF st) {i j : LsIdx}
    {xs : List Level} (hi : denoteLs st i = some xs)
    (hj : denoteLs st j = some xs) : i = j := by
  obtain ⟨us, hvi, hdi⟩ := denoteLs_view hi
  obtain ⟨us', hvj, hdj⟩ := denoteLs_view hj
  have : us = us' := denoteLList_inj h.ls us us' xs hdi hdj
  subst this
  exact h.view_inj hvi hvj

/-- con-leche: ConLeche/Kernel/Expr.lean:136-139 levelsHash and
ConLeche/Kernel/Expr.lean:125-127 levelsHaveParam — the fold of the level
store's exactness over a list. -/
theorem LsStore.derOfView_exact {st : LsStore} (h : LStoreWF st.ls) :
    ∀ (us : List LIdx) (xs : List Level), denoteLList st.ls us = some xs →
      st.derOfView us = ⟨levelsHash xs, levelsHaveParam xs⟩ := by
  intro us
  induction us with
  | nil =>
    intro xs hx
    simp only [denoteLList] at hx
    have hx0 : xs = [] := (Option.some.inj hx).symm
    subst hx0
    rfl
  | cons u r ih =>
    intro xs hx
    simp only [denoteLList, opt2_eq_some_iff] at hx
    obtain ⟨a, as, ha, has, hxs⟩ := hx
    subst hxs
    simp [LsStore.derOfView, LStore.derived_exact h ha, ih as has,
      levelsHash, levelsHaveParam, levelHash]

/-- con-leche: ConLeche/Kernel/Expr.lean:136-139 levelsHash -/
theorem LsStore.derived_exact {st : LsStore} (h : LsStoreWF st) {i : LsIdx}
    {xs : List Level} (hi : denoteLs st i = some xs) :
    st.derived i = ⟨levelsHash xs, levelsHaveParam xs⟩ := by
  obtain ⟨us, hv, hd⟩ := denoteLs_view hi
  rw [h.derExact i us hv]
  exact LsStore.derOfView_exact h.ls us xs hd

/-! ## Expressions

The three stores below the expression store, extracted from `EWFAt`. -/

theorem EWFAt.lssWF {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    LsStoreWF st.lss := h.lss

theorem EWFAt.lsWF {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    LStoreWF st.ls := h.lss.ls

theorem EWFAt.nsWF {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    NStoreWF st.ns := by
  obtain ⟨rkL, hL⟩ := h.lss.ls
  exact hL.ns

/-! ### The fuel disappears -/

theorem denoteEAux_congr {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
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

/-- con-leche: Setlec/Kernel/ArenaWF.lean:477 denote — **the** equation for
`denoteE`. -/
theorem denoteE_unfold {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk)
    {i : EIdx} {v : ENodeView} (hv : st.view i = some v) :
    denoteE st i = denoteEView st v := by
  have hsome : (st.view i).isSome = true := by rw [hv]; rfl
  have hchild : ∀ c ∈ v.echildren, rk c < st.nodeCount := by
    intro c hc
    have h1 := h.childOK i v hv c hc
    have := h.rank_lt h1.1
    omega
  have key : ∀ c ∈ v.echildren,
      denoteEAux st st.nodeCount c = denoteEAux st (st.nodeCount + 1) c := by
    intro c hc
    exact denoteEAux_congr h (st.nodeCount + 1) c st.nodeCount (st.nodeCount + 1)
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

theorem denoteE_view {st : EStore} {i : EIdx} {e : Expr}
    (h : denoteE st i = some e) : ∃ v, st.view i = some v := by
  simp only [denoteE, denoteEAux, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, _⟩ := h
  exact ⟨v, hv⟩

theorem EWFAt.view_inj {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk)
    {i j : EIdx} {v : ENodeView} (hi : st.view i = some v)
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

/-! ### The ten shape lemmas -/

theorem denoteEView_bvar {st : EStore} {v : ENodeView} {k : Nat}
    (h : denoteEView st v = some (.bvar k)) : v = .bvar k := by
  cases v with
  | bvar k' => simp only [denoteEView, Option.some.injEq, Expr.bvar.injEq] at h; subst h; rfl
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_lit {st : EStore} {v : ENodeView} {l : ConLeche.Literal}
    (h : denoteEView st v = some (.lit l)) : v = .lit l := by
  cases v with
  | lit l' => simp only [denoteEView, Option.some.injEq, Expr.lit.injEq] at h; subst h; rfl
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_fvar {st : EStore} {v : ENodeView} {j : Nat} {x : Expr}
    (h : denoteEView st v = some (.fvar j x)) :
    ∃ ty, v = .fvar j ty ∧ denoteE st ty = some x := by
  cases v with
  | fvar j' ty =>
    simp only [denoteEView, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    injection he with e1 e2; subst e1; subst e2
    exact ⟨ty, rfl, hr⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_sort {st : EStore} {v : ENodeView} {a : Level}
    (h : denoteEView st v = some (.sort a)) :
    ∃ u, v = .sort u ∧ denoteL st.ls u = some a := by
  cases v with
  | sort u =>
    simp only [denoteEView, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    injection he with e1; subst e1
    exact ⟨u, rfl, hr⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_const {st : EStore} {v : ENodeView} {nm : ConLeche.Name}
    {us : List Level} (h : denoteEView st v = some (.const nm us)) :
    ∃ n l, v = .const n l ∧ denoteN st.ns n = some nm ∧ denoteLs st.lss l = some us := by
  cases v with
  | const n l =>
    simp only [denoteEView, opt2_eq_some_iff] at h
    obtain ⟨x, y, hx, hy, he⟩ := h
    injection he with e1 e2; subst e1; subst e2
    exact ⟨n, l, rfl, hx, hy⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_app {st : EStore} {v : ENodeView} {x y : Expr}
    (h : denoteEView st v = some (.app x y)) :
    ∃ g a, v = .app g a ∧ denoteE st g = some x ∧ denoteE st a = some y := by
  cases v with
  | app g a =>
    simp only [denoteEView, opt2_eq_some_iff] at h
    obtain ⟨p, q, hp, hq, he⟩ := h
    injection he with e1 e2; subst e1; subst e2
    exact ⟨g, a, rfl, hp, hq⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_lam {st : EStore} {v : ENodeView} {x y : Expr}
    {m : ConLeche.BinderMeta} (h : denoteEView st v = some (.lam x y m)) :
    ∃ ty b, v = .lam ty b m ∧ denoteE st ty = some x ∧ denoteE st b = some y := by
  cases v with
  | lam ty b m' =>
    simp only [denoteEView, opt2_eq_some_iff] at h
    obtain ⟨p, q, hp, hq, he⟩ := h
    injection he with e1 e2 e3; subst e1; subst e2; subst e3
    exact ⟨ty, b, rfl, hp, hq⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_forallE {st : EStore} {v : ENodeView} {x y : Expr}
    {m : ConLeche.BinderMeta} (h : denoteEView st v = some (.forallE x y m)) :
    ∃ ty b, v = .forallE ty b m ∧ denoteE st ty = some x ∧ denoteE st b = some y := by
  cases v with
  | forallE ty b m' =>
    simp only [denoteEView, opt2_eq_some_iff] at h
    obtain ⟨p, q, hp, hq, he⟩ := h
    injection he with e1 e2 e3; subst e1; subst e2; subst e3
    exact ⟨ty, b, rfl, hp, hq⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_letE {st : EStore} {v : ENodeView} {x y z : Expr}
    (h : denoteEView st v = some (.letE x y z)) :
    ∃ ty w b, v = .letE ty w b ∧ denoteE st ty = some x ∧ denoteE st w = some y
      ∧ denoteE st b = some z := by
  cases v with
  | letE ty w b =>
    simp only [denoteEView, opt3_eq_some_iff] at h
    obtain ⟨p, q, r, hp, hq, hr, he⟩ := h
    injection he with e1 e2 e3; subst e1; subst e2; subst e3
    exact ⟨ty, w, b, rfl, hp, hq, hr⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_proj {st : EStore} {v : ENodeView} {nm : ConLeche.Name}
    {j : Nat} {x : Expr} (h : denoteEView st v = some (.proj nm j x)) :
    ∃ n e, v = .proj n j e ∧ denoteN st.ns n = some nm ∧ denoteE st e = some x := by
  cases v with
  | proj n j' e =>
    simp only [denoteEView, opt2_eq_some_iff] at h
    obtain ⟨p, q, hp, hq, he⟩ := h
    injection he with e1 e2 e3; subst e1; subst e2; subst e3
    exact ⟨n, e, rfl, hp, hq⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

/-! ### Injectivity

DESIGN §8.3: "**Exactness (`denote` injective) is a soundness obligation**,
not a performance property: names are compared for inequality throughout the
checker, and `defeqBody`'s `a == b` shortcut […] would still send the arena
into arms the pure run never took if two handles could denote one term." -/

/-- con-leche: Setlec/Kernel/ArenaWF.lean:2758 denote_inj -/
theorem denoteE_inj_at {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    ∀ (x : Expr) (i j : EIdx),
      denoteE st i = some x → denoteE st j = some x → i = j := by
  intro x
  induction x with
  | bvar k =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    rw [denoteEView_bvar hi] at hvi
    rw [denoteEView_bvar hj] at hvj
    exact h.view_inj hvi hvj
  | lit l =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    rw [denoteEView_lit hi] at hvi
    rw [denoteEView_lit hj] at hvj
    exact h.view_inj hvi hvj
  | sort a =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨u, hu, hdu⟩ := denoteEView_sort hi
    obtain ⟨u', hu', hdu'⟩ := denoteEView_sort hj
    have : u = u' := denoteL_inj h.lsWF hdu hdu'
    subst this
    rw [hu] at hvi; rw [hu'] at hvj
    exact h.view_inj hvi hvj
  | const nm us =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨n, l, hn, hdn, hdl⟩ := denoteEView_const hi
    obtain ⟨n', l', hn', hdn', hdl'⟩ := denoteEView_const hj
    have e1 : n = n' := denoteN_inj h.nsWF hdn hdn'
    have e2 : l = l' := denoteLs_inj h.lssWF hdl hdl'
    subst e1; subst e2
    rw [hn] at hvi; rw [hn'] at hvj
    exact h.view_inj hvi hvj
  | fvar j' ty ih =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨t, ht, hdt⟩ := denoteEView_fvar hi
    obtain ⟨t', ht', hdt'⟩ := denoteEView_fvar hj
    have : t = t' := ih t t' hdt hdt'
    subst this
    rw [ht] at hvi; rw [ht'] at hvj
    exact h.view_inj hvi hvj
  | app x y ih1 ih2 =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨g, a, hg, hdg, hda⟩ := denoteEView_app hi
    obtain ⟨g', a', hg', hdg', hda'⟩ := denoteEView_app hj
    have e1 : g = g' := ih1 g g' hdg hdg'
    have e2 : a = a' := ih2 a a' hda hda'
    subst e1; subst e2
    rw [hg] at hvi; rw [hg'] at hvj
    exact h.view_inj hvi hvj
  | lam x y m ih1 ih2 =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨t, b, ht, hdt, hdb⟩ := denoteEView_lam hi
    obtain ⟨t', b', ht', hdt', hdb'⟩ := denoteEView_lam hj
    have e1 : t = t' := ih1 t t' hdt hdt'
    have e2 : b = b' := ih2 b b' hdb hdb'
    subst e1; subst e2
    rw [ht] at hvi; rw [ht'] at hvj
    exact h.view_inj hvi hvj
  | forallE x y m ih1 ih2 =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨t, b, ht, hdt, hdb⟩ := denoteEView_forallE hi
    obtain ⟨t', b', ht', hdt', hdb'⟩ := denoteEView_forallE hj
    have e1 : t = t' := ih1 t t' hdt hdt'
    have e2 : b = b' := ih2 b b' hdb hdb'
    subst e1; subst e2
    rw [ht] at hvi; rw [ht'] at hvj
    exact h.view_inj hvi hvj
  | letE x y z ih1 ih2 ih3 =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨t, w, b, ht, hdt, hdw, hdb⟩ := denoteEView_letE hi
    obtain ⟨t', w', b', ht', hdt', hdw', hdb'⟩ := denoteEView_letE hj
    have e1 : t = t' := ih1 t t' hdt hdt'
    have e2 : w = w' := ih2 w w' hdw hdw'
    have e3 : b = b' := ih3 b b' hdb hdb'
    subst e1; subst e2; subst e3
    rw [ht] at hvi; rw [ht'] at hvj
    exact h.view_inj hvi hvj
  | proj nm j' x ih =>
    intro i j hi hj
    obtain ⟨vi, hvi⟩ := denoteE_view hi
    obtain ⟨vj, hvj⟩ := denoteE_view hj
    rw [denoteE_unfold h hvi] at hi
    rw [denoteE_unfold h hvj] at hj
    obtain ⟨n, e, hn, hdn, hde⟩ := denoteEView_proj hi
    obtain ⟨n', e', hn', hdn', hde'⟩ := denoteEView_proj hj
    have e1 : n = n' := denoteN_inj h.nsWF hdn hdn'
    have e2 : e = e' := ih e e' hde hde'
    subst e1; subst e2
    rw [hn] at hvi; rw [hn'] at hvj
    exact h.view_inj hvi hvj

/-- con-leche: Setlec/Kernel/ArenaWF.lean:2758 denote_inj — **exactness**: on a
well-formed arena, two handles denoting the same expression are equal. -/
theorem denoteE_inj {st : EStore} (h : StoreWF st) {i j : EIdx} {x : Expr}
    (hi : denoteE st i = some x) (hj : denoteE st j = some x) : i = j := by
  obtain ⟨rk, h⟩ := h
  exact denoteE_inj_at h x i j hi hj

/-! ### The derived word is `ConLeche.Expr.data` of the denotation -/

/-- con-leche: ConLeche/Kernel/Expr.lean:356-402 Expr.data — **exactness** of
the packed derived word.  This is the lemma DESIGN §8.3 asks for: "so
`derived st i = (denote st i).data` is an exactness lemma and every pure-side
lemma that reads `data` transfers". -/
theorem EStore.derived_exact_at {st : EStore} {rk : EIdx → Nat}
    (h : EWFAt st rk) : ∀ (x : Expr) (i : EIdx),
      denoteE st i = some x → st.derived i = x.data := by
  intro x
  induction x with
  | bvar k =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    rw [denoteEView_bvar hi] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, Expr.data]
  | lit l =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    rw [denoteEView_lit hi] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, Expr.data]
  | sort a =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨u, hu, hdu⟩ := denoteEView_sort hi
    rw [hu] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.lder, LStore.derived_exact h.lsWF hdu,
      Expr.data, levelHash]
  | const nm us =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨n, l, hn, hdn, hdl⟩ := denoteEView_const hi
    rw [hn] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.nder, EStore.lsder,
      NStore.derived_exact h.nsWF hdn, LsStore.derived_exact h.lssWF hdl,
      Expr.data]
  | fvar j ty ih =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, ht, hdt⟩ := denoteEView_fvar hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, ih t hdt, Expr.data]
  | app x y ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨g, a, hg, hdg, hda⟩ := denoteEView_app hi
    rw [hg] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, ih1 g hdg, ih2 a hda, Expr.data]
  | lam x y m ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, b, ht, hdt, hdb⟩ := denoteEView_lam hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, ih1 t hdt, ih2 b hdb, Expr.data]
  | forallE x y m ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, b, ht, hdt, hdb⟩ := denoteEView_forallE hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, ih1 t hdt, ih2 b hdb, Expr.data]
  | letE x y z ih1 ih2 ih3 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, w, b, ht, hdt, hdw, hdb⟩ := denoteEView_letE hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, ih1 t hdt, ih2 w hdw, ih3 b hdb, Expr.data]
  | proj nm j x ih =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨n, e, hn, hdn, hde⟩ := denoteEView_proj hi
    rw [hn] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.nder, NStore.derived_exact h.nsWF hdn,
      ih e hde, Expr.data]

/-- con-leche: ConLeche/Kernel/Expr.lean:356-402 Expr.data -/
theorem EStore.derived_exact {st : EStore} (h : StoreWF st) {i : EIdx}
    {x : Expr} (hi : denoteE st i = some x) : st.derived i = x.data := by
  obtain ⟨rk, h⟩ := h
  exact EStore.derived_exact_at h x i hi

end ConRon.Arena
