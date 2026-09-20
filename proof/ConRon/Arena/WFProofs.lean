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

/-! ## `tag_cases` — the ten-way tag dispatch, without Mathlib

`ETables.get`, `ETables.derAt` and their three smaller siblings are chains of
`if i.tag == ETag.… then … else …`, one arm per constructor, and almost every
proof below has to take them apart.  Mathlib's `split_ifs` is the tactic for
that, and this library deliberately does not depend on Mathlib (DESIGN §8.3:
`ConRon.Arena` imports `Std` and `ConLeche.Kernel.Expr`, nothing else), so here
is the two-line replacement built out of core's `split`.

* `tag_cases` splits every `if` in the goal, repeatedly.
* `tag_cases h` splits the goal's chain *and* `h`'s together: each branch's
  condition is named `hc`, and the same `if` is reduced in `h` by `if_pos hc` /
  `if_neg hc`.  When the chain is only in `h` it splits `h` and reduces the
  goal instead, so one tactic serves both directions.

The `hygiene false` is what makes `hc` visible to the branch proofs — they use
it as the tag equation (`eq_of_beq hc : i.tag = ETag.bvar`). -/

syntax (name := tagCases) "tag_cases" (ppSpace colGt ident)? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| tag_cases) => `(tactic| repeat' split)
  | `(tactic| tag_cases $h:ident) =>
    `(tactic| repeat' first
        | (split <;> rename_i hc <;> try (first
            | simp only [if_pos hc] at $h:ident
            | simp only [if_neg hc] at $h:ident))
        | (split at $h:ident <;> rename_i hc <;> try (first
            | simp only [if_pos hc]
            | simp only [if_neg hc])))

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


/-! ## Handles: the tier bit, and equality from the three fields -/

/-- A scratch handle's tier bit is `tierS`: `tier` is below 2 and not 0. -/
theorem Idx.tier_eq_tierS {k : IdxKind} {i : Idx k} (h : i.isPersistent = false) :
    i.tier = Idx.tierS := by
  have h2 := Idx.tier_lt i
  apply UInt32.toNat_inj.mp
  show i.tier.toNat = (1 : UInt32).toNat
  have h0 : i.tier ≠ 0 := by
    intro he; simp only [Idx.isPersistent, he] at h; exact absurd h (by decide)
  have h0' : i.tier.toNat ≠ 0 := fun he => h0 (UInt32.toNat_inj.mp (by simpa using he))
  simp only [UInt32.toNat_ofNat]
  omega

/-- A persistent handle's tier bit is `tierP`. -/
theorem Idx.tier_eq_tierP {k : IdxKind} {i : Idx k} (h : i.isPersistent = true) :
    i.tier = Idx.tierP := by
  apply UInt32.toNat_inj.mp
  simp only [Idx.isPersistent, beq_iff_eq] at h
  rw [h]; rfl

/-- `Idx.ext_of` with the index given as the `Nat` the array reads. -/
theorem Idx.eq_of_idxNat {k : IdxKind} {i j : Idx k} (ht : i.tag = j.tag)
    (hr : i.tier = j.tier) (hn : i.idxNat = j.idxNat) : i = j :=
  Idx.ext_of ht hr (UInt32.toNat_inj.mp hn)
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

/-! ## Appending to a table

`Array.push` only *adds* readable indices, so every decoded node keeps
decoding.  That is all `Ext` needs: `denote` is an `Option`, and the
extension relation only claims `= some` is preserved. -/

theorem Option.map_mono {α β : Type} {f : α → β} {o o' : Option α} {b : β}
    (hm : ∀ a, o = some a → o' = some a) (h : o.map f = some b) :
    o'.map f = some b := by
  simp only [Option.map_eq_some_iff] at h ⊢
  obtain ⟨a, ha, he⟩ := h
  exact ⟨a, hm a ha, he⟩

theorem Tbl.node?_push {α ι δ : Type} [BEq α] [Hashable α] {t : Tbl α ι δ}
    {a w : α} {d : δ} {h : ι} {n : Nat} (hn : t.node? n = some a) :
    (t.push w d h).node? n = some a := by
  cases t with | mk ns ds cs =>
  simp only [Tbl.node?, Tbl.push] at hn ⊢
  rw [Array.getElem?_push]
  split
  · rename_i heq; rw [heq] at hn; simp at hn
  · exact hn

theorem Tbl.node?_push_new {α ι δ : Type} [BEq α] [Hashable α] {t : Tbl α ι δ}
    {w : α} {d : δ} {h : ι} : (t.push w d h).node? t.size = some w := by
  cases t
  simp [Tbl.push, Tbl.node?, Tbl.size, Array.getElem?_push]


/-! ### One column: `Tbl` under `push`

Everything the tier lemmas need about a single constructor's array, proved
once over the generic `Tbl`. -/

section Tbl
variable {α ι δ : Type} [BEq α] [Hashable α]

theorem Tbl.size_push (t : Tbl α ι δ) (a : α) (d : δ) (i : ι) :
    (t.push a d i).size = t.size + 1 := by
  cases t; simp [Tbl.push, Tbl.size]

theorem Tbl.node?_push_eq {t : Tbl α ι δ} {a : α} {d : δ} {i : ι} {n : Nat} :
    (t.push a d i).node? n = if n = t.size then some a else t.node? n := by
  cases t; simp only [Tbl.push, Tbl.node?, Tbl.size, Array.getElem?_push]

theorem Tbl.node?_size (t : Tbl α ι δ) : t.node? t.size = none := by
  cases t; simp [Tbl.node?, Tbl.size]

theorem Tbl.lt_of_node? {t : Tbl α ι δ} {n : Nat} {a : α} (h : t.node? n = some a) :
    n < t.size := by
  cases t with | mk ns ds cs =>
  simp only [Tbl.node?, Array.getElem?_eq_some_iff] at h
  exact h.1

theorem Tbl.lt_of_map {β : Type} {t : Tbl α ι δ} {n : Nat} {f : α → β} {b : β}
    (h : (t.node? n).map f = some b) : n < t.size := by
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨a, ha, _⟩ := h
  exact Tbl.lt_of_node? ha

/-- One arm of a tag dispatch, inverted: what a decoded node was before the
table grew. -/
theorem Tbl.map_inv {β : Type} {tb tb' : Tbl α ι δ} {f : α → β} {n : Nat} {v : β}
    {Q : β → Prop} (hh : ∀ a, tb'.node? n = some a → tb.node? n = some a ∨ Q (f a))
    (h : (tb'.node? n).map f = some v) : (tb.node? n).map f = some v ∨ Q v := by
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (hh a ha).imp (fun h' => by rw [h']; rfl) id

theorem Tbl.find?_push [LawfulBEq α] {t : Tbl α ι δ} {a b : α} {d : δ} {i : ι} :
    (t.push a d i).find? b = if (a == b) = true then some i else t.find? b := by
  cases t
  simp only [Tbl.push, Tbl.find?, Std.HashMap.getElem?_insert]

theorem Tbl.Sized_push {t : Tbl α ι δ} {a : α} {d : δ} {i : ι}
    (hs : t.Sized) : (t.push a d i).Sized := by
  cases t; simp_all [Tbl.push, Tbl.Sized]

theorem Tbl.derAt_push_of_lt [Inhabited δ] {t : Tbl α ι δ} {a : α} {d : δ} {i : ι}
    {n : Nat} (hs : t.Sized) (hn : n < t.size) :
    (t.push a d i).derAt n = t.derAt n := by
  cases t with | mk ns ds cs =>
  simp only [Tbl.Sized, Tbl.size] at hs hn
  simp only [Tbl.push, Tbl.derAt, Array.getD_eq_getD_getElem?, Array.getElem?_push]
  rw [if_neg (by omega)]

theorem Tbl.derAt_push_size [Inhabited δ] {t : Tbl α ι δ} {a : α} {d : δ} {i : ι}
    (hs : t.Sized) : (t.push a d i).derAt t.size = d := by
  cases t with | mk ns ds cs =>
  simp only [Tbl.Sized] at hs
  simp only [Tbl.push, Tbl.derAt, Tbl.size, Array.getD_eq_getD_getElem?,
    Array.getElem?_push]
  rw [if_pos hs.symm]
  rfl

theorem Tbl.Sized_empty : (Tbl.empty : Tbl α ι δ).Sized := rfl
theorem Tbl.node?_empty (n : Nat) : (Tbl.empty : Tbl α ι δ).node? n = none := rfl
theorem Tbl.find?_empty (a : α) : (Tbl.empty : Tbl α ι δ).find? a = none := by
  simp [Tbl.empty, Tbl.find?]
theorem Tbl.size_empty : (Tbl.empty : Tbl α ι δ).size = 0 := rfl

end Tbl

/-! ### The expression tier under `push`

`ETables.get_inv` is the tag dispatch done once and for all: a node decoded
from a *grown* tier either decoded from the old one, or is the one that was
appended.  Every later `ETables` lemma is an instance of it or of
`derAt_congr`, so the ten-way `if` chain is taken apart exactly twice. -/

/-- con-leche: none — the constructor tag a node view lands under. -/
def ENodeView.tagOf : ENodeView → UInt32
  | .bvar _ => ETag.bvar
  | .fvar _ _ => ETag.fvar
  | .sort _ => ETag.sort
  | .const _ _ => ETag.const
  | .app _ _ => ETag.app
  | .lam _ _ _ => ETag.lam
  | .forallE _ _ _ => ETag.forallE
  | .letE _ _ _ => ETag.letE
  | .lit _ => ETag.lit
  | .proj _ _ _ => ETag.proj

theorem ENodeView.tagOf_lt (v : ENodeView) : v.tagOf.toNat < 16 := by
  cases v <;> (simp only [ENodeView.tagOf]; decide)

theorem ETables.get_inv {t t' : ETables} {Q : UInt32 → Nat → ENodeView → Prop}
    {i : EIdx} {v : ENodeView}
    (hb : ∀ n a, t'.bvars.node? n = some a →
      t.bvars.node? n = some a ∨ Q ETag.bvar n (.bvar a.i))
    (hfv : ∀ n a, t'.fvars.node? n = some a →
      t.fvars.node? n = some a ∨ Q ETag.fvar n (.fvar a.idx a.ty))
    (hso : ∀ n a, t'.sorts.node? n = some a →
      t.sorts.node? n = some a ∨ Q ETag.sort n (.sort a.u))
    (hco : ∀ n a, t'.consts.node? n = some a →
      t.consts.node? n = some a ∨ Q ETag.const n (.const a.n a.us))
    (hap : ∀ n a, t'.apps.node? n = some a →
      t.apps.node? n = some a ∨ Q ETag.app n (.app a.f a.a))
    (hla : ∀ n a, t'.lams.node? n = some a →
      t.lams.node? n = some a ∨ Q ETag.lam n (.lam a.ty a.body a.m))
    (hfa : ∀ n a, t'.foralls.node? n = some a →
      t.foralls.node? n = some a ∨ Q ETag.forallE n (.forallE a.ty a.body a.m))
    (hle : ∀ n a, t'.lets.node? n = some a →
      t.lets.node? n = some a ∨ Q ETag.letE n (.letE a.ty a.val a.body))
    (hli : ∀ n a, t'.lits.node? n = some a →
      t.lits.node? n = some a ∨ Q ETag.lit n (.lit a.l))
    (hpr : ∀ n a, t'.projs.node? n = some a →
      t.projs.node? n = some a ∨ Q ETag.proj n (.proj a.n a.i a.e))
    (h : t'.get i = some v) : t.get i = some v ∨ Q i.tag i.idxNat v := by
  simp only [ETables.get] at h ⊢
  tag_cases h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hb _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hfv _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hso _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hco _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hap _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hla _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hfa _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hle _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hli _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hpr _) h
  · simp at h

theorem ETables.get_push_inv {t : ETables} {w : ENodeView} {d : UInt64} {tr : UInt32}
    {i : EIdx} {v : ENodeView} (h : (t.push w d tr).1.get i = some v) :
    t.get i = some v ∨ (i.tag = w.tagOf ∧ i.idxNat = t.sizeOf w ∧ v = w) := by
  refine ETables.get_inv (Q := fun tg n v' => tg = w.tagOf ∧ n = t.sizeOf w ∧ v' = w)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
    intro n a ha <;> cases w <;>
    simp only [ETables.push] at ha <;>
    first
      | exact Or.inl ha
      | (rw [Tbl.node?_push_eq] at ha
         split at ha
         · simp only [Option.some.injEq] at ha
           subst ha
           exact Or.inr ⟨rfl, by simp only [ETables.sizeOf]; assumption, rfl⟩
         · exact Or.inl ha)

/-- The index a `push` is about to use reads as absent *before* the push —
which is what makes the appended handle fresh. -/
theorem ETables.get_eq_none_of_size {t : ETables} {w : ENodeView} {i : EIdx}
    (htg : i.tag = w.tagOf) (hix : i.idxNat = t.sizeOf w) : t.get i = none := by
  cases w <;>
    simp only [ENodeView.tagOf] at htg <;>
    simp only [ETables.sizeOf] at hix <;>
    simp [ETables.get, htg, hix, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
      ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj,
      Tbl.node?_size]

theorem ETables.push_tag {t : ETables} {w : ENodeView} {d : UInt64} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.tag = w.tagOf := by
  have hn : ((UInt32.ofNat (t.sizeOf w)).toNat) < Idx.idxCap := by
    rw [Idx.idxCap] at hcap ⊢; simp; omega
  cases w <;>
    simp only [ETables.push, ENodeView.tagOf, ETables.sizeOf] at * <;>
    exact Idx.tag_mk _ _ _ (by decide) htr hn

theorem ETables.push_idxNat {t : ETables} {w : ENodeView} {d : UInt64} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.idxNat = t.sizeOf w := by
  cases w <;>
    simp only [ETables.push, ETables.sizeOf] at * <;>
    exact Idx.idxNat_mk _ _ _ (by decide) htr hcap

theorem ETables.find?_push {t : ETables} {w v : ENodeView} {d : UInt64} {tr : UInt32} :
    (t.push w d tr).1.find? v =
      if w = v then some (t.push w d tr).2 else t.find? v := by
  cases w <;> cases v <;>
    simp only [ETables.push, ETables.find?, Tbl.find?_push, beq_iff_eq,
      BVarNode.mk.injEq, FVarNode.mk.injEq, SortNode.mk.injEq, ConstNode.mk.injEq,
      AppNode.mk.injEq, BindNode.mk.injEq, LetNode.mk.injEq, LitNode.mk.injEq,
      ProjNode.mk.injEq, ENodeView.bvar.injEq, ENodeView.fvar.injEq,
      ENodeView.sort.injEq, ENodeView.const.injEq, ENodeView.app.injEq,
      ENodeView.lam.injEq, ENodeView.forallE.injEq, ENodeView.letE.injEq,
      ENodeView.lit.injEq, ENodeView.proj.injEq, reduceCtorEq, if_false]

theorem ETables.sizeOf_push_cases {t : ETables} {w v : ENodeView} {d : UInt64}
    {tr : UInt32} :
    (t.push w d tr).1.sizeOf v = t.sizeOf v ∨
      ((t.push w d tr).1.sizeOf v = t.sizeOf w + 1 ∧ t.sizeOf v = t.sizeOf w) := by
  cases w <;> cases v <;>
    simp only [ETables.push, ETables.sizeOf] <;>
    first
      | exact Or.inl trivial
      | exact Or.inr ⟨Tbl.size_push _ _ _ _, trivial⟩

theorem ETables.Sized_push {t : ETables} {w : ENodeView} {d : UInt64} {tr : UInt32}
    (hs : t.Sized) : (t.push w d tr).1.Sized := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  cases w <;>
    (simp only [ETables.push, ETables.Sized]
     refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
     first | assumption | exact Tbl.Sized_push (by assumption))

theorem ETables.count_push {t : ETables} {w : ENodeView} {d : UInt64} {tr : UInt32} :
    (t.push w d tr).1.count = t.count + 1 := by
  cases w <;>
    simp [ETables.push, ETables.count, Tbl.size_push] <;> omega

/-- The derived column is read through the same tag dispatch as `get`, so a
column-wise agreement transfers. -/
theorem ETables.derAt_congr {t t' : ETables} {i : EIdx} {v : ENodeView}
    (h : t.get i = some v)
    (hb : ∀ n, n < t.bvars.size → t'.bvars.derAt n = t.bvars.derAt n)
    (hfv : ∀ n, n < t.fvars.size → t'.fvars.derAt n = t.fvars.derAt n)
    (hso : ∀ n, n < t.sorts.size → t'.sorts.derAt n = t.sorts.derAt n)
    (hco : ∀ n, n < t.consts.size → t'.consts.derAt n = t.consts.derAt n)
    (hap : ∀ n, n < t.apps.size → t'.apps.derAt n = t.apps.derAt n)
    (hla : ∀ n, n < t.lams.size → t'.lams.derAt n = t.lams.derAt n)
    (hfa : ∀ n, n < t.foralls.size → t'.foralls.derAt n = t.foralls.derAt n)
    (hle : ∀ n, n < t.lets.size → t'.lets.derAt n = t.lets.derAt n)
    (hli : ∀ n, n < t.lits.size → t'.lits.derAt n = t.lits.derAt n)
    (hpr : ∀ n, n < t.projs.size → t'.projs.derAt n = t.projs.derAt n) :
    t'.derAt i = t.derAt i := by
  simp only [ETables.get] at h
  simp only [ETables.derAt]
  tag_cases h
  · exact hb _ (Tbl.lt_of_map h)
  · exact hfv _ (Tbl.lt_of_map h)
  · exact hso _ (Tbl.lt_of_map h)
  · exact hco _ (Tbl.lt_of_map h)
  · exact hap _ (Tbl.lt_of_map h)
  · exact hla _ (Tbl.lt_of_map h)
  · exact hfa _ (Tbl.lt_of_map h)
  · exact hle _ (Tbl.lt_of_map h)
  · exact hli _ (Tbl.lt_of_map h)
  · exact hpr _ (Tbl.lt_of_map h)
  · simp at h

theorem ETables.derAt_push_of_get {t : ETables} {w : ENodeView} {d : UInt64}
    {tr : UInt32} {i : EIdx} {v : ENodeView} (hs : t.Sized) (h : t.get i = some v) :
    (t.push w d tr).1.derAt i = t.derAt i := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  cases w <;>
    refine ETables.derAt_congr h ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intro n hn <;> simp only [ETables.push] <;>
    first | rfl | exact Tbl.derAt_push_of_lt (by assumption) hn

theorem ETables.derAt_push_new {t : ETables} {w : ENodeView} {d : UInt64}
    {tr : UInt32} (hs : t.Sized) (htr : tr.toNat < 2)
    (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.derAt (t.push w d tr).2 = d := by
  have htag := ETables.push_tag (t := t) (w := w) (d := d) (tr := tr) htr hcap
  have hix := ETables.push_idxNat (t := t) (w := w) (d := d) (tr := tr) htr hcap
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hs
  cases w <;>
    simp only [ENodeView.tagOf] at htag <;>
    simp only [ETables.sizeOf] at hix <;>
    simp only [ETables.derAt, htag, hix, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit, ETag.proj, beq_self_eq_true, if_true] <;>
    (simp only [ETables.push]; exact Tbl.derAt_push_size (by assumption))

theorem ETables.get_empty (i : EIdx) : (ETables.empty).get i = none := by
  simp [ETables.empty, ETables.get, Tbl.empty, Tbl.node?]

theorem ETables.find?_empty (v : ENodeView) : (ETables.empty).find? v = none := by
  cases v <;> simp [ETables.empty, ETables.find?, Tbl.find?_empty]

theorem ETables.sizeOf_empty (v : ENodeView) : (ETables.empty).sizeOf v = 0 := by
  cases v <;> rfl

theorem ETables.count_empty : (ETables.empty).count = 0 := rfl

theorem ETables.Sized_empty : (ETables.empty).Sized :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
/-- The expression tier's `get` is monotone in each of its ten arrays.  The
`by_cases` chain is the tag dispatch, written out because this library
deliberately does not depend on Mathlib (`split_ifs` is a Mathlib tactic). -/
theorem ETables.get_mono {t t' : ETables}
    (hb : ∀ n a, t.bvars.node? n = some a → t'.bvars.node? n = some a)
    (hfv : ∀ n a, t.fvars.node? n = some a → t'.fvars.node? n = some a)
    (hso : ∀ n a, t.sorts.node? n = some a → t'.sorts.node? n = some a)
    (hco : ∀ n a, t.consts.node? n = some a → t'.consts.node? n = some a)
    (hap : ∀ n a, t.apps.node? n = some a → t'.apps.node? n = some a)
    (hla : ∀ n a, t.lams.node? n = some a → t'.lams.node? n = some a)
    (hfa : ∀ n a, t.foralls.node? n = some a → t'.foralls.node? n = some a)
    (hle : ∀ n a, t.lets.node? n = some a → t'.lets.node? n = some a)
    (hli : ∀ n a, t.lits.node? n = some a → t'.lits.node? n = some a)
    (hpr : ∀ n a, t.projs.node? n = some a → t'.projs.node? n = some a)
    {i : EIdx} {v : ENodeView} (h : t.get i = some v) : t'.get i = some v := by
  simp only [ETables.get] at h ⊢
  by_cases c0 : (i.tag == ETag.bvar) = true
  · rw [if_pos c0] at h ⊢; exact Option.map_mono (hb _) h
  rw [if_neg c0] at h ⊢
  by_cases c1 : (i.tag == ETag.fvar) = true
  · rw [if_pos c1] at h ⊢; exact Option.map_mono (hfv _) h
  rw [if_neg c1] at h ⊢
  by_cases c2 : (i.tag == ETag.sort) = true
  · rw [if_pos c2] at h ⊢; exact Option.map_mono (hso _) h
  rw [if_neg c2] at h ⊢
  by_cases c3 : (i.tag == ETag.const) = true
  · rw [if_pos c3] at h ⊢; exact Option.map_mono (hco _) h
  rw [if_neg c3] at h ⊢
  by_cases c4 : (i.tag == ETag.app) = true
  · rw [if_pos c4] at h ⊢; exact Option.map_mono (hap _) h
  rw [if_neg c4] at h ⊢
  by_cases c5 : (i.tag == ETag.lam) = true
  · rw [if_pos c5] at h ⊢; exact Option.map_mono (hla _) h
  rw [if_neg c5] at h ⊢
  by_cases c6 : (i.tag == ETag.forallE) = true
  · rw [if_pos c6] at h ⊢; exact Option.map_mono (hfa _) h
  rw [if_neg c6] at h ⊢
  by_cases c7 : (i.tag == ETag.letE) = true
  · rw [if_pos c7] at h ⊢; exact Option.map_mono (hle _) h
  rw [if_neg c7] at h ⊢
  by_cases c8 : (i.tag == ETag.lit) = true
  · rw [if_pos c8] at h ⊢; exact Option.map_mono (hli _) h
  rw [if_neg c8] at h ⊢
  by_cases c9 : (i.tag == ETag.proj) = true
  · rw [if_pos c9] at h ⊢; exact Option.map_mono (hpr _) h
  rw [if_neg c9] at h ⊢
  exact absurd h (by simp)

theorem ETables.get_push_mono (t : ETables) (w : ENodeView) (d : UInt64)
    (tr : UInt32) {i : EIdx} {v : ENodeView} (h : t.get i = some v) :
    (t.push w d tr).1.get i = some v := by
  cases w <;>
    refine ETables.get_mono ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
    intro n a ha <;> simp only [ETables.push] <;>
    first | exact ha | exact Tbl.node?_push ha

/-! ## `intern`: monotonicity and extension -/

theorem EStore.view_intern_mono (st : EStore) (w : ENodeView) {i : EIdx}
    {v : ENodeView} (h : st.view i = some v) : (st.intern w).1.view i = some v := by
  simp only [EStore.intern]
  split
  · exact h
  · split
    · rename_i hon
      split
      · exact h
      · simp only [EStore.view, hon] at h ⊢
        by_cases hp : i.isPersistent = true
        · rw [if_pos hp] at h ⊢; exact h
        · rw [if_neg hp] at h ⊢; exact ETables.get_push_mono _ _ _ _ h
    · rename_i hoff
      simp only [EStore.view, hoff] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [if_pos hp] at h ⊢; exact ETables.get_push_mono _ _ _ _ h
      · rw [if_neg hp] at h ⊢; exact h

theorem EStore.lss_intern (st : EStore) (w : ENodeView) :
    (st.intern w).1.lss = st.lss := by
  simp only [EStore.intern]
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

theorem EStore.nodeCount_intern_le (st : EStore) (w : ENodeView) :
    st.nodeCount ≤ (st.intern w).1.nodeCount := by
  simp only [EStore.intern]
  split
  · exact Nat.le_refl _
  · split
    · split
      · exact Nat.le_refl _
      · cases w <;>
          simp [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.push,
            ETables.count, Tbl.push, Tbl.size] <;> omega
    · cases w <;>
        simp [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.push,
          ETables.count, Tbl.push, Tbl.size] <;> omega

/-- `denoteEAux` only needs the store's `view` to grow and its sub-stores to
stay put. -/
theorem denoteEAux_store_mono {st st' : EStore}
    (hv : ∀ i v, st.view i = some v → st'.view i = some v)
    (hl : st'.lss = st.lss) :
    ∀ (f : Nat) (i : EIdx) (e : Expr),
      denoteEAux st f i = some e → denoteEAux st' f i = some e := by
  intro f
  induction f with
  | zero => intro i e h; simp [denoteEAux] at h
  | succ k ih =>
    intro i e h
    simp only [denoteEAux, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨v, hvv, h⟩ := h
    refine ⟨v, hv i v hvv, ?_⟩
    have hns : st'.ns = st.ns := by simp [EStore.ns, hl]
    have hls : st'.ls = st.ls := by simp [EStore.ls, hl]
    cases v with
    | bvar _ => exact h
    | lit _ => exact h
    | sort u => rw [hls]; exact h
    | const n l => rw [hns, hl]; exact h
    | fvar j ty =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨q, hq, he⟩ := h
      exact ⟨q, ih ty q hq, he⟩
    | proj n j e' =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, by rw [hns]; exact hx, ih e' y hy, he⟩
    | app a b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih a x hx, ih b y hy, he⟩
    | lam ty b m =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih ty x hx, ih b y hy, he⟩
    | forallE ty b m =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih ty x hx, ih b y hy, he⟩
    | letE ty w b =>
      simp only [opt3_eq_some_iff] at h ⊢
      obtain ⟨x, y, z, hx, hy, hz, he⟩ := h
      exact ⟨x, y, z, ih ty x hx, ih w y hy, ih b z hz, he⟩

/-- con-leche: Verify/SimI.lean:244 Ext — `intern` extends the arena: every
handle that denoted before denotes the same after. -/
theorem EStore.intern_ext (st : EStore) (w : ENodeView) :
    Ext st (st.intern w).1 := by
  refine ⟨?_, ?_⟩
  · rw [EStore.lss_intern]; exact LsExt.refl _
  · intro i e h
    simp only [denoteE] at h ⊢
    have hmono := denoteEAux_store_mono (st := st) (st' := (st.intern w).1)
      (fun _ _ hh => EStore.view_intern_mono st w hh) (EStore.lss_intern st w)
    have h1 : denoteEAux st ((st.intern w).1.nodeCount + 1) i = some e :=
      denoteEAux_mono st (st.nodeCount + 1) ((st.intern w).1.nodeCount + 1) i e
        (by have := EStore.nodeCount_intern_le st w; omega) h
    exact hmono _ i e h1


/-! ## `view` and `derived`, tier by tier -/

theorem EStore.view_pers {st : EStore} {i : EIdx} (hp : i.isPersistent = true) :
    st.view i = st.pers.get i := by simp [EStore.view, hp]

theorem EStore.view_scr {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.view i = st.scr.get i := by
  simp [EStore.view, hp, hon]

theorem EStore.view_off {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.view i = none := by simp [EStore.view, hp, hon]

theorem EStore.derived_pers {st : EStore} {i : EIdx} (hp : i.isPersistent = true) :
    st.derived i = st.pers.derAt i := by simp [EStore.derived, hp]

theorem EStore.derived_scr {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.derived i = st.scr.derAt i := by
  simp [EStore.derived, hp, hon]

/-- `derOfView` reads nothing but the children's derived words — which is why
`derExact` survives both an append and a `dropScratch`. -/
theorem EStore.derOfView_congr {st st' : EStore} {v : ENodeView}
    (he : ∀ c ∈ v.echildren, st'.derived c = st.derived c)
    (hn : ∀ c ∈ v.nchildren, st'.nder c = st.nder c)
    (hl : ∀ c ∈ v.lchildren, st'.lder c = st.lder c)
    (hs : ∀ c ∈ v.lschildren, st'.lsder c = st.lsder c) :
    st'.derOfView v = st.derOfView v := by
  cases v with
  | bvar _ => rfl
  | lit _ => rfl
  | fvar j ty =>
    simp only [EStore.derOfView, he ty (by simp [ENodeView.echildren])]
  | sort u =>
    simp only [EStore.derOfView, hl u (by simp [ENodeView.lchildren])]
  | const n us =>
    simp only [EStore.derOfView, hn n (by simp [ENodeView.nchildren]),
      hs us (by simp [ENodeView.lschildren])]
  | app f a =>
    simp only [EStore.derOfView, he f (by simp [ENodeView.echildren]),
      he a (by simp [ENodeView.echildren])]
  | lam ty b m =>
    simp only [EStore.derOfView, he ty (by simp [ENodeView.echildren]),
      he b (by simp [ENodeView.echildren])]
  | forallE ty b m =>
    simp only [EStore.derOfView, he ty (by simp [ENodeView.echildren]),
      he b (by simp [ENodeView.echildren])]
  | letE ty val b =>
    simp only [EStore.derOfView, he ty (by simp [ENodeView.echildren]),
      he val (by simp [ENodeView.echildren]), he b (by simp [ENodeView.echildren])]
  | proj n j e =>
    simp only [EStore.derOfView, hn n (by simp [ENodeView.nchildren]),
      he e (by simp [ENodeView.echildren])]
/-! ## The scratch-tier bracket

`enableScratch` and `dropScratch` touch only the scratch arrays and the
scratch flag, so a *persistent* handle's `view` is literally unchanged — that
is the whole point of putting the tier bit above the index instead of in the
low bit (DESIGN §8.3, con-leche's lesson 6). -/

theorem EStore.view_dropScratch_pers (st : EStore) {i : EIdx}
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i := by
  simp [EStore.view, EStore.dropScratch, hp]

theorem EStore.view_dropScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : st.dropScratch.view i = none := by
  simp [EStore.view, EStore.dropScratch, hp]

theorem EStore.view_enableScratch_pers (st : EStore) {i : EIdx}
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i := by
  simp [EStore.view, EStore.enableScratch, hp]

theorem EStore.view_enableScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : st.enableScratch.view i = none := by
  simp [EStore.view, EStore.enableScratch, hp, ETables.empty, ETables.get,
    Tbl.empty, Tbl.node?]

/-- A scratch handle denotes nothing once the scratch tier is dropped: this is
the invalidation half of `dropScratch_spec`. -/
theorem denoteE_dropScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : denoteE st.dropScratch i = none := by
  simp only [denoteE, denoteEAux, EStore.view_dropScratch_scr st hp,
    Option.bind_none]

theorem denoteE_enableScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : denoteE st.enableScratch i = none := by
  simp only [denoteE, denoteEAux, EStore.view_enableScratch_scr st hp,
    Option.bind_none]

/-! ## The remaining store-operation specifications

These are the signatures the later phases of task #97 program against.  The
three proofs left open at P2a are recorded in DESIGN.md §"Task #97a" with
their cost estimate; each is a bookkeeping induction over the ten
constructors' arrays, not a new idea — `intern_ext` above is the same
argument carried all the way through. -/

/-! ### The freshly appended node decodes

`ETables.push_spec` is the ten-way tag dispatch done once: the new handle's
tag and index round-trip (`Idx.tag_mk`, `Idx.idxNat_mk`), so `get` finds the
record `Array.push` just wrote (`Tbl.node?_push_new`), and its tier bit is the
tier it was appended to. -/

theorem Idx.isPersistent_mkP {k : IdxKind} (tg n : UInt32) (htg : tg.toNat < 16)
    (hn : n.toNat < idxCap) : (mk (k := k) tg tierP n).isPersistent = true := by
  have h2 : (tierP : UInt32).toNat < 2 := by decide
  show ((mk (k := k) tg tierP n).tier == 0) = true
  rw [tier_mk tg tierP n htg h2 hn]
  decide

theorem Idx.isPersistent_mkS {k : IdxKind} (tg n : UInt32) (htg : tg.toNat < 16)
    (hn : n.toNat < idxCap) : (mk (k := k) tg tierS n).isPersistent = false := by
  have h2 : (tierS : UInt32).toNat < 2 := by decide
  show ((mk (k := k) tg tierS n).tier == 0) = false
  rw [tier_mk tg tierS n htg h2 hn]
  decide

private theorem ofNat_lt_cap {n : Nat} (h : n < Idx.idxCap) :
    (UInt32.ofNat n).toNat < Idx.idxCap := by
  rw [Idx.idxCap] at h ⊢; simp; omega

theorem ETables.push_spec (t : ETables) (w : ENodeView) (d : UInt64) (tr : UInt32)
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.get (t.push w d tr).2 = some w ∧
      (t.push w d tr).2.tier = tr := by
  simp only [ETables.sizeOf] at hcap
  cases w with
  | bvar i =>
    have htg : (ETag.bvar : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | fvar j ty =>
    have htg : (ETag.fvar : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | sort u =>
    have htg : (ETag.sort : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | const n us =>
    have htg : (ETag.const : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | app f a =>
    have htg : (ETag.app : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | lam ty b m =>
    have htg : (ETag.lam : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | forallE ty b m =>
    have htg : (ETag.forallE : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | letE ty v b =>
    have htg : (ETag.letE : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | lit l =>
    have htg : (ETag.lit : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | proj n j e =>
    have htg : (ETag.proj : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]

/-- con-leche: none — `view` of a freshly interned handle is the node that was
interned (DESIGN §8.3's `view`/`intern` pair). -/
theorem EStore.intern_view_spec {st : EStore} {w : ENodeView} (h : StoreWF st)
    (_hv : st.ViewOK w) (hcap : st.capOK w) :
    (st.intern w).1.view (st.intern w).2 = some w := by
  obtain ⟨rk, hwf⟩ := h
  simp only [EStore.capOK] at hcap
  simp only [EStore.intern]
  split
  · rename_i i heq
    exact ((hwf.consP w i).mp heq).1
  · split
    · rename_i hon
      split
      · rename_i i heq
        exact ((hwf.consS w i).mp heq).1
      · rw [if_pos hon] at hcap
        have hspec := ETables.push_spec st.scr w (st.derOfView w) Idx.tierS
          (by decide) hcap
        have hp : ((st.scr.push w (st.derOfView w) Idx.tierS).2).isPersistent = false := by
          show (_ == 0) = false
          rw [hspec.2]; decide
        simp only [EStore.view]
        rw [if_neg (by simp [hp]), if_pos hon]
        exact hspec.1
    · rename_i hoff
      rw [if_neg hoff] at hcap
      have hspec := ETables.push_spec st.pers w (st.derOfView w) Idx.tierP
        (by decide) hcap
      have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [EStore.view]
      rw [if_pos hp]
      exact hspec.1


/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — `intern` preserves the
store invariant. -/
theorem EStore.intern_wf {st : EStore} {w : ENodeView} (h : StoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) : StoreWF (st.intern w).1 := by
  sorry

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — **`intern_spec`**: the
store stays well formed, the arena only grows, the new handle decodes to the
node that was interned, and it denotes that node's denotation. -/
theorem EStore.intern_spec {st : EStore} {w : ENodeView} (h : StoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    StoreWF (st.intern w).1 ∧ Ext st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w ∧
      denoteE (st.intern w).1 (st.intern w).2 = denoteEView (st.intern w).1 w := by
  have hwf := EStore.intern_wf h hv hcap
  have hview := EStore.intern_view_spec h hv hcap
  refine ⟨hwf, EStore.intern_ext st w, hview, ?_⟩
  obtain ⟨rk', hwf'⟩ := hwf
  exact denoteE_unfold hwf' hview

/-- con-leche: Setlec/Kernel/IExpr.lean:472 enableTierTwo -/
theorem EStore.enableScratch_wf {st : EStore} (h : StoreWF st) :
    StoreWF st.enableScratch := by
  sorry

/-- con-leche: Setlec/Kernel/IExpr.lean:472 enableTierTwo — opening the
scratch tier keeps the invariant and changes no persistent handle. -/
theorem EStore.enableScratch_spec {st : EStore} (h : StoreWF st) :
    StoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) ∧
      (∀ i, i.isPersistent = false → denoteE st.enableScratch i = none) :=
  ⟨EStore.enableScratch_wf h, fun i hp => EStore.view_enableScratch_pers st hp,
   fun i hp => denoteE_enableScratch_scr st hp⟩

/-- con-leche: Setlec/Kernel/IExpr.lean:480 truncateTierTwo -/
theorem EStore.dropScratch_wf {st : EStore} (h : StoreWF st) :
    StoreWF st.dropScratch := by
  sorry

/-- con-leche: Setlec/Kernel/IExpr.lean:480 truncateTierTwo — dropping the
scratch tier keeps every persistent denotation and invalidates every scratch
handle. -/
theorem EStore.dropScratch_denote_pers {st : EStore} (h : StoreWF st)
    {i : EIdx} {e : Expr} (hp : i.isPersistent = true)
    (hd : denoteE st i = some e) : denoteE st.dropScratch i = some e := by
  sorry

/-- con-leche: Setlec/Kernel/IExpr.lean:480 truncateTierTwo — **the** tier
discipline in one statement. -/
theorem EStore.dropScratch_spec {st : EStore} (h : StoreWF st) :
    StoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i e, i.isPersistent = true → denoteE st i = some e →
        denoteE st.dropScratch i = some e) ∧
      (∀ i, i.isPersistent = false → denoteE st.dropScratch i = none) :=
  ⟨EStore.dropScratch_wf h, fun i hp => EStore.view_dropScratch_pers st hp,
   fun _ _ hp hd => EStore.dropScratch_denote_pers h hp hd,
   fun i hp => denoteE_dropScratch_scr st hp⟩

/-! ### The same, for the three stores underneath

Names, levels and level lists have the identical shape; their `Ext`,
`intern_spec`, `enableScratch_spec` and `dropScratch_spec` are the same
arguments over three / five / one constructor arrays instead of ten. -/

theorem NStore.intern_spec {st : NStore} {w : NNodeView} (h : NStoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    NStoreWF (st.intern w).1 ∧ NExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w := by
  sorry

theorem LStore.intern_spec {st : LStore} {w : LNodeView} (h : LStoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    LStoreWF (st.intern w).1 ∧ LExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w := by
  sorry

theorem LsStore.intern_spec {st : LsStore} {w : LsNodeView} (h : LsStoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    LsStoreWF (st.intern w).1 ∧ LsExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w := by
  sorry

theorem NStore.dropScratch_spec {st : NStore} (h : NStoreWF st) :
    NStoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i x, i.isPersistent = true → denoteN st i = some x →
        denoteN st.dropScratch i = some x) := by
  sorry

theorem LStore.dropScratch_spec {st : LStore} (h : LStoreWF st) :
    LStoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i x, i.isPersistent = true → denoteL st i = some x →
        denoteL st.dropScratch i = some x) := by
  sorry

theorem LsStore.dropScratch_spec {st : LsStore} (h : LsStoreWF st) :
    LsStoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i x, i.isPersistent = true → denoteLs st i = some x →
        denoteLs st.dropScratch i = some x) := by
  sorry

theorem NStore.enableScratch_spec {st : NStore} (h : NStoreWF st) :
    NStoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) := by
  sorry

theorem LStore.enableScratch_spec {st : LStore} (h : LStoreWF st) :
    LStoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) := by
  sorry

theorem LsStore.enableScratch_spec {st : LsStore} (h : LsStoreWF st) :
    LsStoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) := by
  sorry

end ConRon.Arena
