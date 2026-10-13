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
import ConRon.Arena.WFSkip

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
  condition is named `hc`, and the same `if` is reduced in `h` by `ite_eq_left hc` /
  `ite_eq_right hc`.  When the chain is only in `h` it splits `h` and reduces the
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
            | simp only [ite_eq_left hc] at $h:ident
            | simp only [ite_eq_right hc] at $h:ident))
        | (split at $h:ident <;> rename_i hc <;> try (first
            | simp only [ite_eq_left hc]
            | simp only [ite_eq_right hc])))

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

/-- con-leche: none — arena infrastructure; **the** equation for `denoteN`:
on a well-formed store the fuel is invisible.  Precedent: con-leche's
retired `Setlec/Kernel/ArenaWF.lean:477 denote` (at 94a1cf78). -/
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

/-- con-leche: none — arena infrastructure; the name store's denotation is
injective.  Precedent: con-leche's retired `Setlec/Kernel/ArenaWF.lean:2758
denote_inj` (at 94a1cf78). -/
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

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:2758 denote_inj` (at 94a1cf78). -/
theorem denoteN_inj {st : NStore} (h : NStoreWF st) {i j : NIdx}
    {x : ConLeche.Name} (hi : denoteN st i = some x)
    (hj : denoteN st j = some x) : i = j := by
  obtain ⟨rk, h⟩ := h
  exact denoteN_inj_at h x i j hi hj

/-! ## Names: the derived column is con-leche's cached hash -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-44 Name — the `hashData` computed
field, lines 41-44.  **Exactness** (con-leche's lesson 2: prove exactness,
not soundness): the name store's derived column is the cached hash of the
name the handle denotes. -/
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

/-- con-leche: ConLeche/Kernel/Name.lean:34-44 Name — the `hashData` computed
field, lines 41-44. -/
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

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:477 denote` (at 94a1cf78). -/
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

/-- con-leche: none — arena infrastructure; the level store's denotation is
injective.  Precedent: con-leche's retired `Setlec/Kernel/ArenaWF.lean:2758
denote_inj` (at 94a1cf78). -/
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

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:2758 denote_inj` (at 94a1cf78). -/
theorem denoteL_inj {st : LStore} (h : LStoreWF st) {i j : LIdx} {x : Level}
    (hi : denoteL st i = some x) (hj : denoteL st j = some x) : i = j := by
  obtain ⟨rk, h⟩ := h
  exact denoteL_inj_at h x i j hi hj

/-- con-leche: ConLeche/Kernel/Expr.lean:39-52 Level — the `hashData` computed
field, lines 47-53, and `ConLeche/Kernel/Expr.lean:114-122 levelHasParam`:
exactness of the level store's derived column. -/
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

/-- con-leche: ConLeche/Kernel/Expr.lean:39-52 Level — the `hashData` computed
field, lines 47-53. -/
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

/-- con-leche: none — arena infrastructure; the level-list store's unfolding
equation.  Precedent: con-leche's retired `Setlec/Kernel/ArenaWF.lean:477
denote` (at 94a1cf78). -/
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

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:2758 denote_inj` (at 94a1cf78). -/
theorem denoteLs_inj {st : LsStore} (h : LsStoreWF st) {i j : LsIdx}
    {xs : List Level} (hi : denoteLs st i = some xs)
    (hj : denoteLs st j = some xs) : i = j := by
  obtain ⟨us, hvi, hdi⟩ := denoteLs_view hi
  obtain ⟨us', hvj, hdj⟩ := denoteLs_view hj
  have : us = us' := denoteLList_inj h.ls us us' xs hdi hdj
  subst this
  exact h.view_inj hvi hvj

/-- con-leche: ConLeche/Kernel/Expr.lean:117-120 levelsHash — and
`ConLeche/Kernel/Expr.lean:124-127 levelsHaveParam`: the fold of the level
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

/-- con-leche: ConLeche/Kernel/Expr.lean:117-120 levelsHash -/
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
      | lam ty b =>
        have h1 := hchild ty (by simp [ENodeView.echildren])
        have h2 := hchild b (by simp [ENodeView.echildren])
        simp only [Option.bind_some, ih ty g g' h1.1 h1.2.1 h1.2.2,
          ih b g g' h2.1 h2.2.1 h2.2.2]
      | forallE ty b =>
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

/-- con-leche: none — arena infrastructure; **the** equation for `denoteE`.
Precedent: con-leche's retired `Setlec/Kernel/ArenaWF.lean:477 denote` (at
94a1cf78). -/
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
  | lam ty b =>
    simp only [denoteEView, denoteE]
    rw [key ty (by simp [ENodeView.echildren]), key b (by simp [ENodeView.echildren])]
  | forallE ty b =>
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
    (h : denoteEView st v = some (.lam x y)) :
    ∃ ty b, v = .lam ty b ∧ denoteE st ty = some x ∧ denoteE st b = some y := by
  cases v with
  | lam ty b =>
    simp only [denoteEView, opt2_eq_some_iff] at h
    obtain ⟨p, q, hp, hq, he⟩ := h
    injection he with e1 e2; subst e1; subst e2
    exact ⟨ty, b, rfl, hp, hq⟩
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff]

theorem denoteEView_forallE {st : EStore} {v : ENodeView} {x y : Expr}
    (h : denoteEView st v = some (.forallE x y)) :
    ∃ ty b, v = .forallE ty b ∧ denoteE st ty = some x ∧ denoteE st b = some y := by
  cases v with
  | forallE ty b =>
    simp only [denoteEView, opt2_eq_some_iff] at h
    obtain ⟨p, q, hp, hq, he⟩ := h
    injection he with e1 e2; subst e1; subst e2
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
  | _ => simp_all [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff]

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

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/ArenaWF.lean:2758 denote_inj` (at 94a1cf78). -/
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
  | lam x y ih1 ih2 =>
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
  | forallE x y ih1 ih2 =>
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

/-- con-leche: none — arena infrastructure; **exactness**: on a well-formed
arena, two handles denoting the same expression are equal.  Precedent:
con-leche's retired `Setlec/Kernel/ArenaWF.lean:2758 denote_inj` (at
94a1cf78). -/
theorem denoteE_inj {st : EStore} (h : StoreWF st) {i j : EIdx} {x : Expr}
    (hi : denoteE st i = some x) (hj : denoteE st j = some x) : i = j := by
  obtain ⟨rk, h⟩ := h
  exact denoteE_inj_at h x i j hi hj

/-! ### The derived word is `ConLeche.Expr.data` of the denotation -/

/-- con-leche: ConLeche/Kernel/Expr.lean:256-375 Expr — the `data` computed
field, lines 329-374.  **Exactness** of the packed derived word: this is the
lemma DESIGN §8.3 asks for, "so `derived st i = (denote st i).data` is an
exactness lemma and every pure-side lemma that reads `data` transfers". -/
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
    simp [EStore.derOfView, EStore.derOfBVar, Expr.data]
  | lit l =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    rw [denoteEView_lit hi] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfLit, Expr.data]
  | sort a =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨u, hu, hdu⟩ := denoteEView_sort hi
    rw [hu] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfSort, EStore.lder,
      LStore.derived_exact h.lsWF hdu, Expr.data, levelHash]
  | const nm us =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨n, l, hn, hdn, hdl⟩ := denoteEView_const hi
    rw [hn] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfConst, EStore.nder, EStore.lsder,
      NStore.derived_exact h.nsWF hdn, LsStore.derived_exact h.lssWF hdl,
      Expr.data]
  | fvar j ty ih =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, ht, hdt⟩ := denoteEView_fvar hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfFVar, ih t hdt, Expr.data]
  | app x y ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨g, a, hg, hdg, hda⟩ := denoteEView_app hi
    rw [hg] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfApp, ih1 g hdg, ih2 a hda, Expr.data]
  | lam x y ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, b, ht, hdt, hdb⟩ := denoteEView_lam hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfBindAt, derOfBind, ih1 t hdt, ih2 b hdb,
      Expr.data]
  | forallE x y ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, b, ht, hdt, hdb⟩ := denoteEView_forallE hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfBindAt, derOfBind, ih1 t hdt, ih2 b hdb,
      Expr.data]
  | letE x y z ih1 ih2 ih3 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, w, b, ht, hdt, hdw, hdb⟩ := denoteEView_letE hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfLetAt, derOfLet, ih1 t hdt, ih2 w hdw,
      ih3 b hdb, Expr.data]
  | proj nm j x ih =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨n, e, hn, hdn, hde⟩ := denoteEView_proj hi
    rw [hn] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfProj, EStore.nder,
      NStore.derived_exact h.nsWF hdn, ih e hde, Expr.data]

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
  simp [Tbl.push, Tbl.node?, Tbl.size]


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
  rw [ite_eq_right (by omega)]

theorem Tbl.derAt_push_size [Inhabited δ] {t : Tbl α ι δ} {a : α} {d : δ} {i : ι}
    (hs : t.Sized) : (t.push a d i).derAt t.size = d := by
  cases t with | mk ns ds cs =>
  simp only [Tbl.Sized] at hs
  simp only [Tbl.push, Tbl.derAt, Tbl.size, Array.getD_eq_getD_getElem?,
    Array.getElem?_push]
  rw [ite_eq_left hs.symm]
  rfl

theorem Tbl.find?_empty (a : α) : (Tbl.empty : Tbl α ι δ).find? a = none := by
  simp [Tbl.empty, Tbl.find?]
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
  | .lam _ _ => ETag.lam
  | .forallE _ _ => ETag.forallE
  | .letE _ _ _ => ETag.letE
  | .lit _ => ETag.lit
  | .proj _ _ _ => ETag.proj

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
      t.lams.node? n = some a ∨ Q ETag.lam n (.lam a.ty a.body))
    (hfa : ∀ n a, t'.foralls.node? n = some a →
      t.foralls.node? n = some a ∨ Q ETag.forallE n (.forallE a.ty a.body))
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

theorem ETables.getBind_eq_none_of_size {t : ETables} {w : ENodeView} {i : EIdx}
    (htg : i.tag = w.tagOf) (hix : i.idxNat = t.sizeOf w) : t.getBind i = none := by
  cases w <;>
    simp only [ENodeView.tagOf] at htg <;>
    simp only [ETables.sizeOf] at hix <;>
    simp [ETables.getBind, htg, hix, ETag.bvar, ETag.fvar, ETag.sort, ETag.const,
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
      ENodeView.lit.injEq, ENodeView.proj.injEq, reduceCtorEq, ite_false]

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

/-! The arms of `ETables.derAt`, each read off once. -/

theorem ETables.derAt_bvar {t : ETables} {i : EIdx} (hc : i.tag = ETag.bvar) :
    t.derAt i = t.bvars.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar]

theorem ETables.derAt_fvar {t : ETables} {i : EIdx} (hc : i.tag = ETag.fvar) :
    t.derAt i = t.fvars.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar]

theorem ETables.derAt_sort {t : ETables} {i : EIdx} (hc : i.tag = ETag.sort) :
    t.derAt i = t.sorts.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort]

theorem ETables.derAt_const {t : ETables} {i : EIdx} (hc : i.tag = ETag.const) :
    t.derAt i = t.consts.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort, ETag.const]

theorem ETables.derAt_app {t : ETables} {i : EIdx} (hc : i.tag = ETag.app) :
    t.derAt i = t.apps.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app]

theorem ETables.derAt_lam {t : ETables} {i : EIdx} (hc : i.tag = ETag.lam) :
    t.derAt i = t.lams.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
    ETag.lam]

theorem ETables.derAt_forallE {t : ETables} {i : EIdx} (hc : i.tag = ETag.forallE) :
    t.derAt i = t.foralls.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
    ETag.lam, ETag.forallE]

theorem ETables.derAt_letE {t : ETables} {i : EIdx} (hc : i.tag = ETag.letE) :
    t.derAt i = t.lets.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
    ETag.lam, ETag.forallE, ETag.letE]

theorem ETables.derAt_lit {t : ETables} {i : EIdx} (hc : i.tag = ETag.lit) :
    t.derAt i = t.lits.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
    ETag.lam, ETag.forallE, ETag.letE, ETag.lit]

theorem ETables.derAt_proj {t : ETables} {i : EIdx} (hc : i.tag = ETag.proj) :
    t.derAt i = t.projs.derAt i.idxNat := by
  simp [ETables.derAt, hc, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
    ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]

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
      ETag.lit, ETag.proj, beq_self_eq_true, ite_true] <;>
    (simp only [ETables.push]; exact Tbl.derAt_push_size (by assumption))

theorem ETables.get_empty (i : EIdx) : (ETables.empty).get i = none := by
  simp [ETables.empty, ETables.get, Tbl.empty, Tbl.node?]

theorem ETables.getBind_empty (i : EIdx) : (ETables.empty).getBind i = none := by
  simp [ETables.empty, ETables.getBind, Tbl.empty, Tbl.node?]

theorem ETables.find?_empty (v : ENodeView) : (ETables.empty).find? v = none := by
  cases v <;> simp [ETables.empty, ETables.find?, Tbl.find?_empty]

theorem ETables.sizeOf_empty (v : ENodeView) : (ETables.empty).sizeOf v = 0 := by
  cases v <;> rfl

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
  · rw [ite_eq_left c0] at h ⊢; exact Option.map_mono (hb _) h
  rw [ite_eq_right c0] at h ⊢
  by_cases c1 : (i.tag == ETag.fvar) = true
  · rw [ite_eq_left c1] at h ⊢; exact Option.map_mono (hfv _) h
  rw [ite_eq_right c1] at h ⊢
  by_cases c2 : (i.tag == ETag.sort) = true
  · rw [ite_eq_left c2] at h ⊢; exact Option.map_mono (hso _) h
  rw [ite_eq_right c2] at h ⊢
  by_cases c3 : (i.tag == ETag.const) = true
  · rw [ite_eq_left c3] at h ⊢; exact Option.map_mono (hco _) h
  rw [ite_eq_right c3] at h ⊢
  by_cases c4 : (i.tag == ETag.app) = true
  · rw [ite_eq_left c4] at h ⊢; exact Option.map_mono (hap _) h
  rw [ite_eq_right c4] at h ⊢
  by_cases c5 : (i.tag == ETag.lam) = true
  · rw [ite_eq_left c5] at h ⊢; exact Option.map_mono (hla _) h
  rw [ite_eq_right c5] at h ⊢
  by_cases c6 : (i.tag == ETag.forallE) = true
  · rw [ite_eq_left c6] at h ⊢; exact Option.map_mono (hfa _) h
  rw [ite_eq_right c6] at h ⊢
  by_cases c7 : (i.tag == ETag.letE) = true
  · rw [ite_eq_left c7] at h ⊢; exact Option.map_mono (hle _) h
  rw [ite_eq_right c7] at h ⊢
  by_cases c8 : (i.tag == ETag.lit) = true
  · rw [ite_eq_left c8] at h ⊢; exact Option.map_mono (hli _) h
  rw [ite_eq_right c8] at h ⊢
  by_cases c9 : (i.tag == ETag.proj) = true
  · rw [ite_eq_left c9] at h ⊢; exact Option.map_mono (hpr _) h
  rw [ite_eq_right c9] at h ⊢
  exact absurd h (by simp)

theorem ETables.getBind_mono {t t' : ETables}
    (hla : ∀ n a, t.lams.node? n = some a → t'.lams.node? n = some a)
    (hfa : ∀ n a, t.foralls.node? n = some a → t'.foralls.node? n = some a)
    {i : EIdx} {p : EIdx × EIdx} (h : t.getBind i = some p) :
    t'.getBind i = some p := by
  simp only [ETables.getBind] at h ⊢
  by_cases c5 : (i.tag == ETag.lam) = true
  · rw [ite_eq_left c5] at h ⊢; exact Option.map_mono (hla _) h
  rw [ite_eq_right c5] at h ⊢
  by_cases c6 : (i.tag == ETag.forallE) = true
  · rw [ite_eq_left c6] at h ⊢; exact Option.map_mono (hfa _) h
  rw [ite_eq_right c6] at h ⊢
  exact absurd h (by simp)

theorem ETables.get_push_mono (t : ETables) (w : ENodeView) (d : UInt64)
    (tr : UInt32) {i : EIdx} {v : ENodeView} (h : t.get i = some v) :
    (t.push w d tr).1.get i = some v := by
  cases w <;>
    refine ETables.get_mono ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
    intro n a ha <;> simp only [ETables.push] <;>
    first | exact ha | exact Tbl.node?_push ha

theorem ETables.getBind_push_mono (t : ETables) (w : ENodeView) (d : UInt64)
    (tr : UInt32) {i : EIdx} {p : EIdx × EIdx}
    (h : t.getBind i = some p) : (t.push w d tr).1.getBind i = some p := by
  cases w <;>
    refine ETables.getBind_mono ?_ ?_ h <;>
    intro n a ha <;> simp only [ETables.push] <;>
    first | exact ha | exact Tbl.node?_push ha

/-! ### `view`, tier by tier -/

theorem EStore.view_pers {st : EStore} {i : EIdx} (hp : i.isPersistent = true) :
    st.view i = st.pers.get i := by simp [EStore.view, hp]

theorem EStore.view_scr {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.view i = st.scr.get i := by
  simp [EStore.view, hp, hon]

theorem EStore.view_off {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.view i = none := by
  simp [EStore.view, hp, hon]

/-! ### `intern` -/

theorem EStore.view_mono_of_tiers (st st' : EStore)
    (hs : st'.scratchOn = st.scratchOn)
    (hpg : ∀ i v, st.pers.get i = some v → st'.pers.get i = some v)
    (hsg : ∀ i v, st.scr.get i = some v → st'.scr.get i = some v)
    {i : EIdx} {v : ENodeView} (h : st.view i = some v) : st'.view i = some v := by
  by_cases hp : i.isPersistent = true
  · rw [EStore.view_pers hp] at h
    rw [EStore.view_pers hp]
    exact hpg _ _ h
  · have hp' : i.isPersistent = false := by simpa using hp
    by_cases hon : st.scratchOn = true
    · rw [EStore.view_scr hp' hon] at h
      rw [EStore.view_scr hp' (by rw [hs]; exact hon)]
      exact hsg _ _ h
    · rw [EStore.view_off hp' (by simpa using hon)] at h
      exact absurd h (by simp)

/-- `intern` leaves the store in one of three shapes — untouched, one array of
the scratch tier appended to, or one array of the persistent tier — and this
is the only place its `match` chain is taken apart. -/
theorem EStore.intern_cases (st : EStore) (v : ENodeView) :
    (st.intern v).1 = st ∨
      (st.intern v).1 =
        { st with scr := (st.scr.push v (st.derOfView v) Idx.tierS).1 } ∨
      (st.intern v).1 =
        { st with pers := (st.pers.push v (st.derOfView v) Idx.tierP).1 } := by
  unfold EStore.intern
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem EStore.view_intern_mono (st : EStore) (w : ENodeView) {i : EIdx}
    {v : ENodeView} (h : st.view i = some v) : (st.intern w).1.view i = some v := by
  rcases EStore.intern_cases st w with he | he | he <;> rw [he]
  · exact h
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => ETables.get_push_mono _ _ _ _ hh
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => ETables.get_push_mono _ _ _ _ hh
    · exact fun _ _ hh => hh

theorem EStore.lss_intern (st : EStore) (w : ENodeView) :
    (st.intern w).1.lss = st.lss := by
  rcases EStore.intern_cases st w with he | he | he <;> rw [he]

theorem EStore.nodeCount_intern_le (st : EStore) (w : ENodeView) :
    st.nodeCount ≤ (st.intern w).1.nodeCount := by
  rcases EStore.intern_cases st w with he | he | he <;> rw [he]
  · exact Nat.le_refl _
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_push]
    omega
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_push]
    omega

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
    | lam ty b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih ty x hx, ih b y hy, he⟩
    | forallE ty b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih ty x hx, ih b y hy, he⟩
    | letE ty w b =>
      simp only [opt3_eq_some_iff] at h ⊢
      obtain ⟨x, y, z, hx, hy, hz, he⟩ := h
      exact ⟨x, y, z, ih ty x hx, ih w y hy, ih b z hz, he⟩

/-- con-leche: none — arena infrastructure; `intern` extends the arena:
every handle that denoted before denotes the same after.  Precedent:
con-leche's retired `Verify/SimI.lean:244 Ext` (at 94a1cf78). -/
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
    simp only [EStore.derOfView, EStore.derOfFVar,
      he ty (by simp [ENodeView.echildren])]
  | sort u =>
    simp only [EStore.derOfView, EStore.derOfSort,
      hl u (by simp [ENodeView.lchildren])]
  | const n us =>
    simp only [EStore.derOfView, EStore.derOfConst,
      hn n (by simp [ENodeView.nchildren]), hs us (by simp [ENodeView.lschildren])]
  | app f a =>
    simp only [EStore.derOfView, EStore.derOfApp,
      he f (by simp [ENodeView.echildren]), he a (by simp [ENodeView.echildren])]
  | lam ty b =>
    simp only [EStore.derOfView, EStore.derOfBindAt,
      he ty (by simp [ENodeView.echildren]), he b (by simp [ENodeView.echildren])]
  | forallE ty b =>
    simp only [EStore.derOfView, EStore.derOfBindAt,
      he ty (by simp [ENodeView.echildren]), he b (by simp [ENodeView.echildren])]
  | letE ty val b =>
    simp only [EStore.derOfView, EStore.derOfLetAt, derOfLet,
      he ty (by simp [ENodeView.echildren]), he val (by simp [ENodeView.echildren]),
      he b (by simp [ENodeView.echildren])]
  | proj n j e =>
    simp only [EStore.derOfView, EStore.derOfProj,
      hn n (by simp [ENodeView.nchildren]), he e (by simp [ENodeView.echildren])]

/-! ## The scratch-tier bracket

`enableScratch` and `dropScratch` touch only the scratch arrays and the
scratch flag, so a *persistent* handle's `view` is unchanged — that is the
whole point of putting the tier bit above the index instead of in the low bit
(DESIGN §8.3, con-leche's lesson 6). -/

theorem EStore.view_dropScratch_pers (st : EStore) {i : EIdx}
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i := by
  rw [EStore.view_pers (st := st.dropScratch) hp, EStore.view_pers (st := st) hp]
  rfl

theorem EStore.view_dropScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : st.dropScratch.view i = none :=
  EStore.view_off hp rfl

theorem EStore.view_enableScratch_pers (st : EStore) {i : EIdx}
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i := by
  rw [EStore.view_pers (st := st.enableScratch) hp, EStore.view_pers (st := st) hp]
  rfl

theorem EStore.view_enableScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : st.enableScratch.view i = none := by
  rw [EStore.view_scr (st := st.enableScratch) hp rfl]
  exact ETables.get_empty _

theorem EStore.view_dropScratch_pers_wf {st : EStore} (_h : StoreWF st) {i : EIdx}
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i :=
  EStore.view_dropScratch_pers st hp

theorem EStore.view_enableScratch_pers_wf {st : EStore} (_h : StoreWF st) {i : EIdx}
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i :=
  EStore.view_enableScratch_pers st hp

theorem denoteE_dropScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : denoteE st.dropScratch i = none := by
  simp only [denoteE, denoteEAux, EStore.view_dropScratch_scr st hp,
    Option.bind_none]

theorem denoteE_enableScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : denoteE st.enableScratch i = none := by
  simp only [denoteE, denoteEAux, EStore.view_enableScratch_scr st hp,
    Option.bind_none]

/-! ### Names -/

theorem NTables.get_empty (i : NIdx) : (NTables.empty).get i = none := by
  simp [NTables.empty, NTables.get, Tbl.empty, Tbl.node?]

theorem NTables.find?_empty (v : NNodeView) : (NTables.empty).find? v = none := by
  cases v <;> simp [NTables.empty, NTables.find?, Tbl.find?_empty]

theorem NTables.sizeOf_empty (v : NNodeView) : (NTables.empty).sizeOf v = 0 := by
  cases v <;> rfl

theorem NTables.Sized_empty : (NTables.empty).Sized := ⟨rfl, rfl, rfl⟩

theorem NStore.view_pers {st : NStore} {i : NIdx} (hp : i.isPersistent = true) :
    st.view i = st.pers.get i := by simp [NStore.view, hp]

theorem NStore.view_scr {st : NStore} {i : NIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.view i = st.scr.get i := by
  simp [NStore.view, hp, hon]

theorem NStore.view_off {st : NStore} {i : NIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.view i = none := by simp [NStore.view, hp, hon]

theorem NStore.derived_pers {st : NStore} {i : NIdx} (hp : i.isPersistent = true) :
    st.derived i = st.pers.derAt i := by simp [NStore.derived, hp]

theorem NStore.derived_scr {st : NStore} {i : NIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.derived i = st.scr.derAt i := by
  simp [NStore.derived, hp, hon]

theorem NStore.derOfView_congr {st st' : NStore} {v : NNodeView}
    (hd : ∀ c ∈ v.children, st'.derived c = st.derived c) :
    st'.derOfView v = st.derOfView v := by
  cases v with
  | anonymous => rfl
  | str p s => simp only [NStore.derOfView, hd p (by simp [NNodeView.children])]
  | num p n => simp only [NStore.derOfView, hd p (by simp [NNodeView.children])]

/-- Emptying the scratch tier keeps the invariant, at the same rank. -/
theorem NStore.wf_of_scr_empty {st st' : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk)
    (hpers : st'.pers = st.pers) (hscr : st'.scr = NTables.empty) :
    NWFAt st' rk := by
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp; rw [NStore.view_pers hp, NStore.view_pers hp, hpers]
  have hviewN : ∀ i, i.isPersistent = false → st'.view i = none := by
    intro i hp
    by_cases hon : st'.scratchOn = true
    · rw [NStore.view_scr hp hon, hscr]; exact NTables.get_empty i
    · exact NStore.view_off hp (by simpa using hon)
  have hpersOf : ∀ i v, st'.view i = some v → i.isPersistent = true := by
    intro i v hi
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hi; exact absurd hi (by simp)
  have hiff : ∀ i v, st'.view i = some v ↔ (st.view i = some v ∧ i.isPersistent = true) := by
    intro i v
    constructor
    · intro hi
      have hp := hpersOf i v hi
      exact ⟨by rwa [hviewP i hp] at hi, hp⟩
    · rintro ⟨hi, hp⟩; rw [hviewP i hp]; exact hi
  have hder : ∀ i, i.isPersistent = true → st'.derived i = st.derived i := by
    intro i hp; rw [NStore.derived_pers hp, NStore.derived_pers hp, hpers]
  have hpc : st'.persCount = st.persCount := by simp only [NStore.persCount, hpers]
  refine { childOK := ?childOK, rankP := ?rankP, rankS := ?rankS, consP := ?consP,
           consS := ?consS, fresh := ?fresh, derExact := ?derExact,
           sizedP := ?sizedP, sizedS := ?sizedS, capP := ?capP, capS := ?capS,
           scrOff := ?scrOff }
  case childOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.childOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2.2 hp
    refine ⟨?_, hch.2.1, fun _ => hcp⟩
    rw [hviewP c hcp]; exact hch.1
  case rankP =>
    intro i hp hi
    rw [hpc]
    exact h.rankP i hp (by rwa [hviewP i hp] at hi)
  case rankS =>
    intro i hp hi
    rw [hviewN i hp] at hi; exact absurd hi (by simp)
  case consP =>
    intro v i
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP v i).mp hf
      exact ⟨(hiff i v).mpr ⟨h1, h2⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP v i).mpr ((hiff i v).mp h1)
  case consS =>
    intro v i
    rw [hscr, NTables.find?_empty]
    constructor
    · intro hf; exact absurd hf (by simp)
    · rintro ⟨h1, h2⟩
      rw [hpersOf i v h1] at h2; exact absurd h2 (by simp)
  case fresh =>
    intro v i hf
    rw [hscr, NTables.find?_empty] at hf; exact absurd hf (by simp)
  case derExact =>
    intro i v hi
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    rw [NStore.derOfView_congr
      (fun c hc => hder c ((h.childOK i v hi' c hc).2.2 hp)), hder i hp]
    exact h.derExact i v hi'
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact NTables.Sized_empty
  case capP => rw [hpers]; exact h.capP
  case capS => intro v; rw [hscr, NTables.sizeOf_empty]; exact Nat.zero_le _
  case scrOff => intro _; exact hscr

theorem NStore.view_dropScratch_pers (st : NStore) {i : NIdx}
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i := by
  simp [NStore.view, NStore.dropScratch, hp]

theorem NStore.view_enableScratch_pers (st : NStore) {i : NIdx}
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i := by
  simp [NStore.view, NStore.enableScratch, hp]

theorem NStore.dropScratch_wfAt {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    NWFAt st.dropScratch rk := NStore.wf_of_scr_empty (NWFAt'.of_wf h) rfl rfl

theorem NStore.enableScratch_wfAt {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    NWFAt st.enableScratch rk := NStore.wf_of_scr_empty (NWFAt'.of_wf h) rfl rfl

/-- A persistent name keeps its readback across `dropScratch`: the recursion
never leaves the persistent tier, because a persistent node's children are
persistent. -/
theorem denoteNAux_dropScratch {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
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

theorem denoteN_dropScratch_pers {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk)
    {i : NIdx} {x : ConLeche.Name} (hp : i.isPersistent = true)
    (hd : denoteN st i = some x) : denoteN st.dropScratch i = some x := by
  have h' := NStore.dropScratch_wfAt h
  obtain ⟨v, hv⟩ := denoteN_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [NStore.view_dropScratch_pers st hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := h.rank_lt (by rw [hv]; rfl)
  have h1 : denoteNAux st.dropScratch (st.nodeCount + 1) i = some x :=
    denoteNAux_dropScratch h _ i x hp hd
  rw [denoteN, denoteNAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

theorem NStore.derived_dropScratch_pers (st : NStore) {i : NIdx}
    (hp : i.isPersistent = true) : st.dropScratch.derived i = st.derived i := by
  rw [NStore.derived_pers hp, NStore.derived_pers hp]; rfl

theorem NStore.derived_enableScratch_pers (st : NStore) {i : NIdx}
    (hp : i.isPersistent = true) : st.enableScratch.derived i = st.derived i := by
  rw [NStore.derived_pers hp, NStore.derived_pers hp]; rfl

/-! ### Levels -/

theorem LTables.get_empty (i : LIdx) : (LTables.empty).get i = none := by
  simp [LTables.empty, LTables.get, Tbl.empty, Tbl.node?]

theorem LTables.find?_empty (v : LNodeView) : (LTables.empty).find? v = none := by
  cases v <;> simp [LTables.empty, LTables.find?, Tbl.find?_empty]

theorem LTables.sizeOf_empty (v : LNodeView) : (LTables.empty).sizeOf v = 0 := by
  cases v <;> rfl

theorem LTables.Sized_empty : (LTables.empty).Sized := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem LStore.view_pers {st : LStore} {i : LIdx} (hp : i.isPersistent = true) :
    st.view i = st.pers.get i := by simp [LStore.view, hp]

theorem LStore.view_scr {st : LStore} {i : LIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.view i = st.scr.get i := by
  simp [LStore.view, hp, hon]

theorem LStore.view_off {st : LStore} {i : LIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.view i = none := by simp [LStore.view, hp, hon]

theorem LStore.derived_pers {st : LStore} {i : LIdx} (hp : i.isPersistent = true) :
    st.derived i = st.pers.derAt i := by simp [LStore.derived, hp]

theorem LStore.derived_scr {st : LStore} {i : LIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.derived i = st.scr.derAt i := by
  simp [LStore.derived, hp, hon]

theorem LStore.derOfView_congr {st st' : LStore} {v : LNodeView}
    (hl : ∀ c ∈ v.lchildren, st'.derived c = st.derived c)
    (hn : ∀ c ∈ v.nchildren, st'.ns.derived c = st.ns.derived c) :
    st'.derOfView v = st.derOfView v := by
  cases v with
  | zero => rfl
  | succ u => simp only [LStore.derOfView, hl u (by simp [LNodeView.lchildren])]
  | max u w =>
    simp only [LStore.derOfView, hl u (by simp [LNodeView.lchildren]),
      hl w (by simp [LNodeView.lchildren])]
  | imax u w =>
    simp only [LStore.derOfView, hl u (by simp [LNodeView.lchildren]),
      hl w (by simp [LNodeView.lchildren])]
  | param n => simp only [LStore.derOfView, hn n (by simp [LNodeView.nchildren])]

theorem LStore.wf_of_scr_empty {st st' : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk)
    (hpers : st'.pers = st.pers) (hscr : st'.scr = LTables.empty)
    (hnsWF : NStoreWF st'.ns)
    (hnsv : ∀ c : NIdx, c.isPersistent = true → st'.ns.view c = st.ns.view c)
    (hnsd : ∀ c : NIdx, c.isPersistent = true → st'.ns.derived c = st.ns.derived c)
    (hsync : st'.scratchOn = st'.ns.scratchOn) :
    LWFAt st' rk := by
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp; rw [LStore.view_pers hp, LStore.view_pers hp, hpers]
  have hviewN : ∀ i, i.isPersistent = false → st'.view i = none := by
    intro i hp
    by_cases hon : st'.scratchOn = true
    · rw [LStore.view_scr hp hon, hscr]; exact LTables.get_empty i
    · exact LStore.view_off hp (by simpa using hon)
  have hpersOf : ∀ i v, st'.view i = some v → i.isPersistent = true := by
    intro i v hi
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hi; exact absurd hi (by simp)
  have hiff : ∀ i v, st'.view i = some v ↔ (st.view i = some v ∧ i.isPersistent = true) := by
    intro i v
    refine ⟨fun hi => ⟨by rwa [hviewP i (hpersOf i v hi)] at hi, hpersOf i v hi⟩, ?_⟩
    rintro ⟨hi, hp⟩; rw [hviewP i hp]; exact hi
  have hder : ∀ i, i.isPersistent = true → st'.derived i = st.derived i := by
    intro i hp; rw [LStore.derived_pers hp, LStore.derived_pers hp, hpers]
  have hpc : st'.persCount = st.persCount := by simp only [LStore.persCount, hpers]
  refine { ns := hnsWF, childOK := ?childOK, nchildOK := ?nchildOK, rankP := ?rankP,
           rankS := ?rankS, consP := ?consP, consS := ?consS, fresh := ?fresh,
           derExact := ?derExact, sizedP := ?sizedP, sizedS := ?sizedS,
           capP := ?capP, capS := ?capS, scrOff := ?scrOff, sync := hsync }
  case childOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.childOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2.2 hp
    refine ⟨?_, hch.2.1, fun _ => hcp⟩
    rw [hviewP c hcp]; exact hch.1
  case nchildOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.nchildOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2 hp
    exact ⟨by rw [hnsv c hcp]; exact hch.1, fun _ => hcp⟩
  case rankP =>
    intro i hp hi
    rw [hpc]
    exact h.rankP i hp (by rwa [hviewP i hp] at hi)
  case rankS =>
    intro i hp hi
    rw [hviewN i hp] at hi; exact absurd hi (by simp)
  case consP =>
    intro v i
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP v i).mp hf
      exact ⟨(hiff i v).mpr ⟨h1, h2⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP v i).mpr ((hiff i v).mp h1)
  case consS =>
    intro v i
    rw [hscr, LTables.find?_empty]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hpersOf i v h1] at h2; exact absurd h2 (by simp)
  case fresh =>
    intro v i hf
    rw [hscr, LTables.find?_empty] at hf; exact absurd hf (by simp)
  case derExact =>
    intro i v hi
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    rw [LStore.derOfView_congr
      (fun c hc => hder c ((h.childOK i v hi' c hc).2.2 hp))
      (fun c hc => hnsd c ((h.nchildOK i v hi' c hc).2 hp)), hder i hp]
    exact h.derExact i v hi'
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact LTables.Sized_empty
  case capP => rw [hpers]; exact h.capP
  case capS => intro v; rw [hscr, LTables.sizeOf_empty]; exact Nat.zero_le _
  case scrOff => intro _; exact hscr

theorem LStore.view_dropScratch_pers (st : LStore) {i : LIdx}
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i := by
  simp [LStore.view, LStore.dropScratch, hp]

theorem LStore.view_enableScratch_pers (st : LStore) {i : LIdx}
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i := by
  simp [LStore.view, LStore.enableScratch, hp]

theorem LStore.derived_dropScratch_pers (st : LStore) {i : LIdx}
    (hp : i.isPersistent = true) : st.dropScratch.derived i = st.derived i := by
  rw [LStore.derived_pers hp, LStore.derived_pers hp]; rfl

theorem LStore.derived_enableScratch_pers (st : LStore) {i : LIdx}
    (hp : i.isPersistent = true) : st.enableScratch.derived i = st.derived i := by
  rw [LStore.derived_pers hp, LStore.derived_pers hp]; rfl

theorem LStore.dropScratch_wfAt {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    LWFAt st.dropScratch rk := by
  obtain ⟨rkn, hn⟩ := h.ns
  exact LStore.wf_of_scr_empty (LWFAt'.of_wf h) rfl rfl ⟨rkn, NStore.dropScratch_wfAt hn⟩
    (fun c hp => NStore.view_dropScratch_pers st.ns hp)
    (fun c hp => NStore.derived_dropScratch_pers st.ns hp) rfl

theorem LStore.enableScratch_wfAt {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    LWFAt st.enableScratch rk := by
  obtain ⟨rkn, hn⟩ := h.ns
  exact LStore.wf_of_scr_empty (LWFAt'.of_wf h) rfl rfl ⟨rkn, NStore.enableScratch_wfAt hn⟩
    (fun c hp => NStore.view_enableScratch_pers st.ns hp)
    (fun c hp => NStore.derived_enableScratch_pers st.ns hp) rfl

theorem denoteLAux_dropScratch {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
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
      exact denoteN_dropScratch_pers hn
        ((h.nchildOK i _ hv n (by simp [LNodeView.nchildren])).2 hp) hq

theorem denoteL_dropScratch_pers {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk)
    {i : LIdx} {x : Level} (hp : i.isPersistent = true)
    (hd : denoteL st i = some x) : denoteL st.dropScratch i = some x := by
  have h' := LStore.dropScratch_wfAt h
  obtain ⟨v, hv⟩ := denoteL_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [LStore.view_dropScratch_pers st hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := h.rank_lt (by rw [hv]; rfl)
  have h1 : denoteLAux st.dropScratch (st.nodeCount + 1) i = some x :=
    denoteLAux_dropScratch h _ i x hp hd
  rw [denoteL, denoteLAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

/-! ### Level lists -/

theorem LsTables.get_empty (i : LsIdx) : (LsTables.empty).get i = none := by
  simp [LsTables.empty, LsTables.get, Tbl.empty, Tbl.node?]

theorem LsTables.find?_empty (v : LsNodeView) : (LsTables.empty).find? v = none := by
  simp [LsTables.empty, LsTables.find?, Tbl.find?_empty]

theorem LsTables.sizeOf_empty (v : LsNodeView) : (LsTables.empty).sizeOf v = 0 := rfl

theorem LsTables.Sized_empty : (LsTables.empty).Sized := rfl

theorem LsStore.view_pers {st : LsStore} {i : LsIdx} (hp : i.isPersistent = true) :
    st.view i = st.pers.get i := by simp [LsStore.view, hp]

theorem LsStore.view_scr {st : LsStore} {i : LsIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.view i = st.scr.get i := by
  simp [LsStore.view, hp, hon]

theorem LsStore.view_off {st : LsStore} {i : LsIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.view i = none := by
  simp [LsStore.view, hp, hon]

theorem LsStore.derived_pers {st : LsStore} {i : LsIdx} (hp : i.isPersistent = true) :
    st.derived i = st.pers.derAt i := by simp [LsStore.derived, hp]

theorem LsStore.derived_scr {st : LsStore} {i : LsIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.derived i = st.scr.derAt i := by
  simp [LsStore.derived, hp, hon]

theorem LsStore.derOfView_congr {st st' : LsStore} :
    ∀ (v : LsNodeView), (∀ c ∈ v, st'.ls.derived c = st.ls.derived c) →
      st'.derOfView v = st.derOfView v := by
  intro v
  induction v with
  | nil => intro _; rfl
  | cons u us ih =>
    intro hd
    simp only [LsStore.derOfView, hd u (by simp), ih (fun c hc => hd c (by simp [hc]))]

theorem LsStore.wf_of_scr_empty {st st' : LsStore} (h : LsWF' st)
    (hpers : st'.pers = st.pers) (hscr : st'.scr = LsTables.empty)
    (hlsWF : LStoreWF st'.ls)
    (hlv : ∀ c : LIdx, c.isPersistent = true → st'.ls.view c = st.ls.view c)
    (hld : ∀ c : LIdx, c.isPersistent = true → st'.ls.derived c = st.ls.derived c)
    (hsync : st'.scratchOn = st'.ls.scratchOn) :
    LsWF st' := by
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp; rw [LsStore.view_pers hp, LsStore.view_pers hp, hpers]
  have hviewN : ∀ i, i.isPersistent = false → st'.view i = none := by
    intro i hp
    by_cases hon : st'.scratchOn = true
    · rw [LsStore.view_scr hp hon, hscr]; exact LsTables.get_empty i
    · exact LsStore.view_off hp (by simpa using hon)
  have hpersOf : ∀ i v, st'.view i = some v → i.isPersistent = true := by
    intro i v hi
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hi; exact absurd hi (by simp)
  have hiff : ∀ i v, st'.view i = some v ↔ (st.view i = some v ∧ i.isPersistent = true) := by
    intro i v
    refine ⟨fun hi => ⟨by rwa [hviewP i (hpersOf i v hi)] at hi, hpersOf i v hi⟩, ?_⟩
    rintro ⟨hi, hp⟩; rw [hviewP i hp]; exact hi
  have hder : ∀ i, i.isPersistent = true → st'.derived i = st.derived i := by
    intro i hp; rw [LsStore.derived_pers hp, LsStore.derived_pers hp, hpers]
  refine { ls := hlsWF, lchildOK := ?lchildOK, consP := ?consP, consS := ?consS,
           fresh := ?fresh, derExact := ?derExact, sizedP := ?sizedP,
           sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff,
           sync := hsync }
  case lchildOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.lchildOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2 hp
    exact ⟨by rw [hlv c hcp]; exact hch.1, fun _ => hcp⟩
  case consP =>
    intro v i
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP v i).mp hf
      exact ⟨(hiff i v).mpr ⟨h1, h2⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP v i).mpr ((hiff i v).mp h1)
  case consS =>
    intro v i
    rw [hscr, LsTables.find?_empty]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hpersOf i v h1] at h2; exact absurd h2 (by simp)
  case fresh =>
    intro v i hf
    rw [hscr, LsTables.find?_empty] at hf; exact absurd hf (by simp)
  case derExact =>
    intro i v hi
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    rw [LsStore.derOfView_congr v
      (fun c hc => hld c ((h.lchildOK i v hi' c hc).2 hp)), hder i hp]
    exact h.derExact i v hi'
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact LsTables.Sized_empty
  case capP => rw [hpers]; exact h.capP
  case capS => intro v; rw [hscr, LsTables.sizeOf_empty]; exact Nat.zero_le _
  case scrOff => intro _; exact hscr

theorem LsStore.view_dropScratch_pers (st : LsStore) {i : LsIdx}
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i := by
  simp [LsStore.view, LsStore.dropScratch, hp]

theorem LsStore.view_enableScratch_pers (st : LsStore) {i : LsIdx}
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i := by
  simp [LsStore.view, LsStore.enableScratch, hp]

theorem LsStore.dropScratch_wf {st : LsStore} (h : LsWF st) : LsWF st.dropScratch := by
  obtain ⟨rkl, hl⟩ := h.ls
  exact LsStore.wf_of_scr_empty (LsWF'.of_wf h) rfl rfl ⟨rkl, LStore.dropScratch_wfAt hl⟩
    (fun c hp => LStore.view_dropScratch_pers st.ls hp)
    (fun c hp => LStore.derived_dropScratch_pers st.ls hp) rfl

theorem LsStore.enableScratch_wf {st : LsStore} (h : LsWF st) :
    LsWF st.enableScratch := by
  obtain ⟨rkl, hl⟩ := h.ls
  exact LsStore.wf_of_scr_empty (LsWF'.of_wf h) rfl rfl ⟨rkl, LStore.enableScratch_wfAt hl⟩
    (fun c hp => LStore.view_enableScratch_pers st.ls hp)
    (fun c hp => LStore.derived_enableScratch_pers st.ls hp) rfl

theorem denoteLList_dropScratch {ls : LStore} {rk : LIdx → Nat} (h : LWFAt ls rk) :
    ∀ (us : List LIdx) (xs : List Level), (∀ c ∈ us, c.isPersistent = true) →
      denoteLList ls us = some xs → denoteLList ls.dropScratch us = some xs := by
  intro us
  induction us with
  | nil => intro xs _ hd; exact hd
  | cons u rest ih =>
    intro xs hp hd
    simp only [denoteLList, opt2_eq_some_iff] at hd ⊢
    obtain ⟨a, b, ha, hb, he⟩ := hd
    exact ⟨a, b, denoteL_dropScratch_pers h (hp u (by simp)) ha,
      ih b (fun c hc => hp c (by simp [hc])) hb, he⟩

theorem denoteLs_dropScratch_pers {st : LsStore} (h : LsWF st) {i : LsIdx}
    {xs : List Level} (hp : i.isPersistent = true) (hd : denoteLs st i = some xs) :
    denoteLs st.dropScratch i = some xs := by
  obtain ⟨rkl, hl⟩ := h.ls
  obtain ⟨us, hus, hlist⟩ := denoteLs_view hd
  rw [denoteLs, LsStore.view_dropScratch_pers st hp, hus]
  exact denoteLList_dropScratch hl us xs
    (fun c hc => (h.lchildOK i us hus c hc).2 hp) hlist

/-! ### Forgetting the freshness clauses at the expression store

`Arena/WF.lean` has the other three `of_wf`. -/

theorem EWFAt'.of_wf {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    EWFAt' st rk :=
  { lss := LsStoreWF'.of_wf h.lss, childOK := h.childOK, nchildOK := h.nchildOK,
    lchildOK := h.lchildOK, lschildOK := h.lschildOK, rankP := h.rankP,
    rankS := h.rankS, consP := h.consP,
    consSof := fun v i hf => (h.consS v i).mp hf,
    derExact := h.derExact, sizedP := h.sizedP, sizedS := h.sizedS,
    capP := h.capP, capS := h.capS, scrOff := h.scrOff, sync := h.sync }

theorem StoreWF'.of_wf {st : EStore} (h : StoreWF st) : StoreWF' st :=
  let ⟨rk, h⟩ := h; ⟨rk, EWFAt'.of_wf h⟩

theorem EStore.wf_of_scr_empty {st st' : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk)
    (hpers : st'.pers = st.pers) (hscr : st'.scr = ETables.empty)
    (hlssWF : LsStoreWF st'.lss)
    (hnsv : ∀ c : NIdx, c.isPersistent = true → st'.ns.view c = st.ns.view c)
    (hlv : ∀ c : LIdx, c.isPersistent = true → st'.ls.view c = st.ls.view c)
    (hlsv : ∀ c : LsIdx, c.isPersistent = true → st'.lss.view c = st.lss.view c)
    (hnsd : ∀ c : NIdx, c.isPersistent = true → st'.nder c = st.nder c)
    (hld : ∀ c : LIdx, c.isPersistent = true → st'.lder c = st.lder c)
    (hlsd : ∀ c : LsIdx, c.isPersistent = true → st'.lsder c = st.lsder c)
    (hsync : st'.scratchOn = st'.lss.scratchOn) :
    EWFAt st' rk := by
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp
    rw [EStore.view_pers hp, EStore.view_pers hp, hpers]
  have hviewN : ∀ i, i.isPersistent = false → st'.view i = none := by
    intro i hp
    cases hc : st'.scratchOn with
    | false => exact EStore.view_off hp hc
    | true => rw [EStore.view_scr hp hc, hscr]; exact ETables.get_empty i
  have hpersOf : ∀ i v, st'.view i = some v → i.isPersistent = true := by
    intro i v hi
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hi; exact absurd hi (by simp)
  have hiff : ∀ i v, st'.view i = some v ↔
      (st.view i = some v ∧ i.isPersistent = true) := by
    intro i v
    refine ⟨fun hi => ⟨by rwa [hviewP i (hpersOf i v hi)] at hi, hpersOf i v hi⟩, ?_⟩
    rintro ⟨hi, hp⟩; rw [hviewP i hp]; exact hi
  have hder : ∀ i, i.isPersistent = true → st'.derived i = st.derived i := by
    intro i hp; rw [EStore.derived_pers hp, EStore.derived_pers hp, hpers]
  have hpc : st'.persCount = st.persCount := by simp only [EStore.persCount, hpers]
  have hscrFind : ∀ v : ENodeView, st'.scrFind? v = none := by
    intro v
    simp only [EStore.scrFind?, hscr]
    exact ETables.find?_empty v
  have hfind : ∀ v : ENodeView, st'.persFind? v = st.persFind? v := by
    intro v
    simp only [EStore.persFind?, hpers]
  refine { lss := hlssWF, childOK := ?childOK, nchildOK := ?nchildOK,
           lchildOK := ?lchildOK, lschildOK := ?lschildOK, rankP := ?rankP,
           rankS := ?rankS, consP := ?consP,
           consS := ?consS, fresh := ?fresh,
           derExact := ?derExact,
           sizedP := ?sizedP, sizedS := ?sizedS,
           capP := ?capP, capS := ?capS,
           scrOff := ?scrOff, sync := hsync }
  case childOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.childOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2.2 hp
    refine ⟨?_, hch.2.1, fun _ => hcp⟩
    rw [hviewP c hcp]; exact hch.1
  case nchildOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.nchildOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2 hp
    exact ⟨by rw [hnsv c hcp]; exact hch.1, fun _ => hcp⟩
  case lchildOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.lchildOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2 hp
    exact ⟨by rw [hlv c hcp]; exact hch.1, fun _ => hcp⟩
  case lschildOK =>
    intro i v hi c hc
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    have hch := h.lschildOK i v hi' c hc
    have hcp : c.isPersistent = true := hch.2 hp
    exact ⟨by rw [hlsv c hcp]; exact hch.1, fun _ => hcp⟩
  case rankP =>
    intro i hp hi
    rw [hpc]
    exact h.rankP i hp (by rwa [hviewP i hp] at hi)
  case rankS =>
    intro i hp hi
    rw [hviewN i hp] at hi; exact absurd hi (by simp)
  case consP =>
    intro v i
    rw [hfind]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP v i).mp hf
      exact ⟨(hiff i v).mpr ⟨h1, h2⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP v i).mpr ((hiff i v).mp h1)
  case consS =>
    intro v i
    rw [hscrFind v]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hpersOf i v h1] at h2; exact absurd h2 (by simp)
  case fresh =>
    intro v i hf
    rw [hscrFind v] at hf; exact absurd hf (by simp)
  case derExact =>
    intro i v hi
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    rw [EStore.derOfView_congr
      (fun c hc => hder c ((h.childOK i v hi' c hc).2.2 hp))
      (fun c hc => hnsd c ((h.nchildOK i v hi' c hc).2 hp))
      (fun c hc => hld c ((h.lchildOK i v hi' c hc).2 hp))
      (fun c hc => hlsd c ((h.lschildOK i v hi' c hc).2 hp)), hder i hp]
    exact h.derExact i v hi'
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact ETables.Sized_empty
  case capP => rw [hpers]; exact h.capP
  case capS => intro v; rw [hscr, ETables.sizeOf_empty]; exact Nat.zero_le _
  case scrOff => intro _; exact hscr

theorem EStore.dropScratch_wfAt {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    EWFAt st.dropScratch rk := by
  have hlsw : LsWF st.lss := h.lss
  refine EStore.wf_of_scr_empty (EWFAt'.of_wf h) rfl rfl (LsStore.dropScratch_wf hlsw)
    (fun c hp => NStore.view_dropScratch_pers st.ns hp)
    (fun c hp => LStore.view_dropScratch_pers st.ls hp)
    (fun c hp => LsStore.view_dropScratch_pers st.lss hp)
    (fun c hp => NStore.derived_dropScratch_pers st.ns hp)
    (fun c hp => LStore.derived_dropScratch_pers st.ls hp)
    ?_ rfl
  intro c hp
  show (st.lss.dropScratch).derived c = st.lss.derived c
  rw [LsStore.derived_pers hp, LsStore.derived_pers hp]; rfl

theorem EStore.enableScratch_wfAt {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    EWFAt st.enableScratch rk := by
  have hlsw : LsWF st.lss := h.lss
  refine EStore.wf_of_scr_empty (EWFAt'.of_wf h) rfl rfl (LsStore.enableScratch_wf hlsw)
    (fun c hp => NStore.view_enableScratch_pers st.ns hp)
    (fun c hp => LStore.view_enableScratch_pers st.ls hp)
    (fun c hp => LsStore.view_enableScratch_pers st.lss hp)
    (fun c hp => NStore.derived_enableScratch_pers st.ns hp)
    (fun c hp => LStore.derived_enableScratch_pers st.ls hp)
    ?_ rfl
  intro c hp
  show (st.lss.enableScratch).derived c = st.lss.derived c
  rw [LsStore.derived_pers hp, LsStore.derived_pers hp]; rfl

theorem denoteEAux_dropScratch {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    ∀ (f : Nat) (i : EIdx) (x : Expr), i.isPersistent = true →
      denoteEAux st f i = some x → denoteEAux st.dropScratch f i = some x := by
  have hlsw : LsWF st.lss := h.lss
  obtain ⟨rkl, hl⟩ : LStoreWF st.ls := hlsw.ls
  obtain ⟨rkn, hn⟩ : NStoreWF st.ns := hl.ns
  intro f
  induction f with
  | zero => intro i x _ hd; simp [denoteEAux] at hd
  | succ k ih =>
    intro i x hp hd
    simp only [denoteEAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hv, hd⟩ := hd
    refine ⟨v, by rw [EStore.view_dropScratch_pers st hp]; exact hv, ?_⟩
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
      exact denoteL_dropScratch_pers hl
        ((h.lchildOK i _ hv u (by simp [ENodeView.lchildren])).2 hp) hq
    | const n us =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      refine ⟨a, b, ?_, ?_, he⟩
      · exact denoteN_dropScratch_pers hn
          ((h.nchildOK i _ hv n (by simp [ENodeView.nchildren])).2 hp) ha
      · exact denoteLs_dropScratch_pers hlsw
          ((h.lschildOK i _ hv us (by simp [ENodeView.lschildren])).2 hp) hb
    | app g a =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih g p ((h.childOK i _ hv g (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih a q ((h.childOK i _ hv a (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | lam ty b =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨p, q, hp1, hq1, he⟩ := hd
      exact ⟨p, q, ih ty p ((h.childOK i _ hv ty (by simp [ENodeView.echildren])).2.2 hp) hp1,
        ih b q ((h.childOK i _ hv b (by simp [ENodeView.echildren])).2.2 hp) hq1, he⟩
    | forallE ty b =>
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
      exact denoteN_dropScratch_pers hn
        ((h.nchildOK i _ hv n (by simp [ENodeView.nchildren])).2 hp) hp1

/-! ### The freshly appended node decodes

`ETables.push_spec` is the ten-way tag dispatch done once: the new handle's
tag and index round-trip (`Idx.tag_mk`, `Idx.idxNat_mk`), so `get` finds the
record `Array.push` just wrote (`Tbl.node?_push_new`), and its tier bit is the
tier it was appended to. -/

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
      simp [ETag.bvar, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | fvar j ty =>
    have htg : (ETag.fvar : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | sort u =>
    have htg : (ETag.sort : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | const n us =>
    have htg : (ETag.const : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | app f a =>
    have htg : (ETag.app : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
        Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | lam ty b =>
    have htg : (ETag.lam : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | forallE ty b =>
    have htg : (ETag.forallE : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | letE ty v b =>
    have htg : (ETag.letE : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | lit l =>
    have htg : (ETag.lit : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, Tbl.node?_push_new]
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


/-! ## `intern` preserves the invariant

Two lemmas, one per tier the append can land in.  They are stated over an
abstract result store `st'` and an abstract appended tier `tb` with the
`push` as a hypothesis, so that the `intern` case analysis below only has to
supply `rfl`s — and so that neither proof ever has to look inside
`ETables.push` again.

The rank of the new node is the old store's node count (scratch) or
persistent count (persistent), and the rank function is extended by

    rk' c = if the *old* store cannot decode `c` then that count else rk c

which needs no `c ≠ inew` side condition: the appended handle is exactly the
one the old store could not decode (`ETables.get_eq_none_of_size`). -/

/-- con-leche: none — arena infrastructure; appending to the scratch tier
keeps `StoreWF`.  Precedent: con-leche's retired
`Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem EStore.wf_push_scr {st st' : EStore} {rk : EIdx → Nat} {w : ENodeView}
    {tb : ETables} {inew : EIdx}
    (h : EWFAt st rk) (hv : st.ViewOK w)
    (hon : st.scratchOn = true) (hon' : st'.scratchOn = true)
    (hlss : st'.lss = st.lss) (hpers : st'.pers = st.pers)
    (hpush : st.scr.push w (st.derOfView w) Idx.tierS = (tb, inew))
    (hscr : st'.scr = tb)
    (hcap : st.scr.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) (hfs : st.scr.find? w = none) :
    StoreWF st' ∧ st'.view inew = some w ∧ inew.isPersistent = false := by
  have htr : (Idx.tierS : UInt32).toNat < 2 := by decide
  have htb : (st.scr.push w (st.derOfView w) Idx.tierS).1 = tb := by rw [hpush]
  have hid : (st.scr.push w (st.derOfView w) Idx.tierS).2 = inew := by rw [hpush]
  -- the appended column, read back
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (ETables.push_spec st.scr w _ Idx.tierS htr hcap).1
  have hnp : inew.isPersistent = false := by
    show (inew.tier == 0) = false
    rw [← hid, (ETables.push_spec st.scr w _ Idx.tierS htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact ETables.push_tag htr hcap
  have hix : inew.idxNat = st.scr.sizeOf w := by
    rw [← hid]; exact ETables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.scr.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact ETables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.scr.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.scr.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact ETables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.scr.find? u := by
    intro u; rw [← htb, ← hid]; exact ETables.find?_push
  have hdertb : ∀ i u, st.scr.get i = some u → tb.derAt i = st.scr.derAt i := by
    intro i u hi; rw [← htb]; exact ETables.derAt_push_of_get h.sizedS hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact ETables.derAt_push_new h.sizedS htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact ETables.Sized_push h.sizedS
  have hcounttb : tb.count = st.scr.count + 1 := by rw [← htb]; exact ETables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases ETables.sizeOf_push_cases (t := st.scr) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierS) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capS u
    · rw [h1]; omega
  -- the two tiers, as `view` sees them
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp; rw [EStore.view_pers hp, EStore.view_pers hp, hpers]
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = tb.get i := by
    intro i hp; rw [EStore.view_scr hp hon', hscr]
  have hnew_none : st.view inew = none := by
    rw [EStore.view_scr hnp hon]; exact ETables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp]; exact hu
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp']
      exact hmonotb i u (by rwa [EStore.view_scr hp' hon] at hu)
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact Or.inl (by rwa [hviewP i hp] at hu)
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [EStore.view_scr hp' hon]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierS hp').trans (Idx.tier_eq_tierS hnp).symm)
          (h3.trans hix.symm), h4⟩
  -- counts
  have hpc : st'.persCount = st.persCount := by simp only [EStore.persCount, hpers]
  have hnc : st'.nodeCount = st.nodeCount + 1 := by
    simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, hpers, hscr,
      hcounttb]
    omega
  -- derived words
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp : i.isPersistent = true
    · rw [EStore.derived_pers hp, EStore.derived_pers hp, hpers]
    · have hp' : i.isPersistent = false := by simpa using hp
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [EStore.derived_scr hp' hon', EStore.derived_scr hp' hon, hscr]
      exact hdertb i u (by rwa [EStore.view_scr hp' hon] at hu)
  have hns : st'.ns = st.ns := by simp only [EStore.ns, hlss]
  have hls : st'.ls = st.ls := by simp only [EStore.ls, hlss]
  have hdov : ∀ u : ENodeView, (∀ c ∈ u.echildren, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u := by
    intro u hu
    refine EStore.derOfView_congr (fun c hc => hder c (hu c hc)) ?_ ?_ ?_ <;>
      intro c _ <;>
      simp only [EStore.nder, EStore.lder, EStore.lsder, hns, hls, hlss]
  -- the rank
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.nodeCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.nodeCount else rk inew)
      = st.nodeCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, (if (st.view c).isNone = true then st.nodeCount else rk c)
      ≤ st.nodeCount := by
    intro c
    by_cases hc : (st.view c).isSome = true
    · rw [hrkold c hc]; exact Nat.le_of_lt (h.rank_lt hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨?wf, by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
  case wf =>
  refine ⟨fun c => if (st.view c).isNone = true then st.nodeCount else rk c,
    { lss := ?lss, childOK := ?childOK, nchildOK := ?nchildOK,
      lchildOK := ?lchildOK, lschildOK := ?lschildOK,
      rankP := ?rankP, rankS := ?rankS, consP := ?consP, consS := ?consS,
      fresh := ?fresh, derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff,
      sync := by rw [hon', hlss, ← h.sync, hon] }⟩
  case lss => rw [hlss]; exact h.lss
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv.expr c hc
      refine ⟨hmoneS c hcs, ?_, ?_⟩
      · rw [hrkold c hcs, hrknew]; exact h.rank_lt hcs
      · intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case nchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hns]; exact h.nchildOK i u hi' c hc
    · refine ⟨by rw [hns]; exact hv.nm c hc, ?_⟩
      intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case lchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hls]; exact h.lchildOK i u hi' c hc
    · refine ⟨by rw [hls]; exact hv.lvl c hc, ?_⟩
      intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case lschildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hlss]; exact h.lschildOK i u hi' c hc
    · refine ⟨by rw [hlss]; exact hv.lst c hc, ?_⟩
      intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case rankP =>
    intro i hp hi
    have hi' : (st.view i).isSome = true := by rw [← hviewP i hp]; exact hi
    rw [hrkold i hi', hpc]
    exact h.rankP i hp hi'
  case rankS =>
    intro i _ _
    have := hrkle i
    omega
  case consP =>
    intro u i
    simp only [EStore.persFind?]
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
      exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP u i).mpr ⟨by rwa [hviewP i h2] at h1, h2⟩
  case consS =>
    intro u i
    simp only [EStore.scrFind?]
    rw [hscr, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consS u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; simp only [EStore.scrFind?] at hf; rw [hfs] at hf
          exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case fresh =>
    intro u i hf
    simp only [EStore.persFind?, EStore.scrFind?] at hf ⊢
    rw [hscr, hfindtb u] at hf
    rw [hpers]
    by_cases hw : w = u
    · subst hw; exact hfp
    · rw [ite_eq_right hw] at hf; exact h.fresh u i hf
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.expr, EStore.derived_scr hnp hon', hscr, hdernew]
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact hsizedtb
  case capP => rw [hpers]; exact h.capP
  case capS => rw [hscr]; exact hcaptb
  case scrOff => intro hoff; rw [hon'] at hoff; exact absurd hoff (by simp)


/-! ## `intern` on the name store -/

/-- con-leche: none — the constructor tag a name node view lands under. -/
def NNodeView.tagOf : NNodeView → UInt32
  | .anonymous => NTag.anonymous
  | .str _ _ => NTag.str
  | .num _ _ => NTag.num

theorem NTables.get_inv {t t' : NTables} {Q : UInt32 → Nat → NNodeView → Prop}
    {i : NIdx} {v : NNodeView}
    (han : ∀ n a, t'.anons.node? n = some a →
      t.anons.node? n = some a ∨ Q NTag.anonymous n .anonymous)
    (hst : ∀ n a, t'.strs.node? n = some a →
      t.strs.node? n = some a ∨ Q NTag.str n (.str a.pre a.s))
    (hnu : ∀ n a, t'.nums.node? n = some a →
      t.nums.node? n = some a ∨ Q NTag.num n (.num a.pre a.n))
    (h : t'.get i = some v) : t.get i = some v ∨ Q i.tag i.idxNat v := by
  simp only [NTables.get] at h ⊢
  tag_cases h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (han _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hst _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hnu _) h
  · simp at h

theorem NTables.get_push_inv {t : NTables} {w : NNodeView} {d : UInt64} {tr : UInt32}
    {i : NIdx} {v : NNodeView} (h : (t.push w d tr).1.get i = some v) :
    t.get i = some v ∨ (i.tag = w.tagOf ∧ i.idxNat = t.sizeOf w ∧ v = w) := by
  refine NTables.get_inv (Q := fun tg n v' => tg = w.tagOf ∧ n = t.sizeOf w ∧ v' = w)
    ?_ ?_ ?_ h <;>
    intro n a ha <;> cases w <;>
    simp only [NTables.push] at ha <;>
    first
      | exact Or.inl ha
      | (rw [Tbl.node?_push_eq] at ha
         split at ha
         · refine Or.inr ⟨rfl, by simp only [NTables.sizeOf]; assumption, ?_⟩
           simp only [Option.some.injEq] at ha
           first | (subst ha; rfl) | rfl
         · exact Or.inl ha)

theorem NTables.get_eq_none_of_size {t : NTables} {w : NNodeView} {i : NIdx}
    (htg : i.tag = w.tagOf) (hix : i.idxNat = t.sizeOf w) : t.get i = none := by
  cases w <;>
    simp only [NNodeView.tagOf] at htg <;>
    simp only [NTables.sizeOf] at hix <;>
    simp [NTables.get, htg, hix, NTag.anonymous, NTag.str, NTag.num, Tbl.node?_size]

theorem NTables.get_mono {t t' : NTables}
    (han : ∀ n a, t.anons.node? n = some a → t'.anons.node? n = some a)
    (hst : ∀ n a, t.strs.node? n = some a → t'.strs.node? n = some a)
    (hnu : ∀ n a, t.nums.node? n = some a → t'.nums.node? n = some a)
    {i : NIdx} {v : NNodeView} (h : t.get i = some v) : t'.get i = some v := by
  simp only [NTables.get] at h ⊢
  tag_cases h
  · exact Option.map_mono (han _) h
  · exact Option.map_mono (hst _) h
  · exact Option.map_mono (hnu _) h
  · simp at h

theorem NTables.get_push_mono (t : NTables) (w : NNodeView) (d : UInt64)
    (tr : UInt32) {i : NIdx} {v : NNodeView} (h : t.get i = some v) :
    (t.push w d tr).1.get i = some v := by
  cases w <;>
    refine NTables.get_mono ?_ ?_ ?_ h <;>
    intro n a ha <;> simp only [NTables.push] <;>
    first | exact ha | exact Tbl.node?_push ha

theorem NTables.push_spec (t : NTables) (w : NNodeView) (d : UInt64) (tr : UInt32)
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.get (t.push w d tr).2 = some w ∧
      (t.push w d tr).2.tier = tr := by
  simp only [NTables.sizeOf] at hcap
  cases w with
  | anonymous =>
    have htg : (NTag.anonymous : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [NTables.push, NTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [NTag.anonymous, Tbl.node?_push_new]
    · simp only [NTables.push, Idx.tier_mk _ _ _ htg htr hn]
  | str p sv =>
    have htg : (NTag.str : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [NTables.push, NTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [NTag.anonymous, NTag.str, Tbl.node?_push_new]
    · simp only [NTables.push, Idx.tier_mk _ _ _ htg htr hn]
  | num p k =>
    have htg : (NTag.num : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [NTables.push, NTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [NTag.anonymous, NTag.str, NTag.num, Tbl.node?_push_new]
    · simp only [NTables.push, Idx.tier_mk _ _ _ htg htr hn]

theorem NTables.push_tag {t : NTables} {w : NNodeView} {d : UInt64} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.tag = w.tagOf := by
  have hn : ((UInt32.ofNat (t.sizeOf w)).toNat) < Idx.idxCap := by
    rw [Idx.idxCap] at hcap ⊢; simp; omega
  cases w <;>
    simp only [NTables.push, NNodeView.tagOf, NTables.sizeOf] at * <;>
    exact Idx.tag_mk _ _ _ (by decide) htr hn

theorem NTables.push_idxNat {t : NTables} {w : NNodeView} {d : UInt64} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.idxNat = t.sizeOf w := by
  cases w <;>
    simp only [NTables.push, NTables.sizeOf] at * <;>
    exact Idx.idxNat_mk _ _ _ (by decide) htr hcap

theorem NTables.find?_push {t : NTables} {w v : NNodeView} {d : UInt64} {tr : UInt32} :
    (t.push w d tr).1.find? v =
      if w = v then some (t.push w d tr).2 else t.find? v := by
  cases w <;> cases v <;>
    simp only [NTables.push, NTables.find?, Tbl.find?_push, beq_iff_eq,
      StrNode.mk.injEq, NumNode.mk.injEq, NNodeView.str.injEq, NNodeView.num.injEq,
      reduceCtorEq, ite_false, ite_true] <;>
    rfl

theorem NTables.sizeOf_push_cases {t : NTables} {w v : NNodeView} {d : UInt64}
    {tr : UInt32} :
    (t.push w d tr).1.sizeOf v = t.sizeOf v ∨
      ((t.push w d tr).1.sizeOf v = t.sizeOf w + 1 ∧ t.sizeOf v = t.sizeOf w) := by
  cases w <;> cases v <;>
    simp only [NTables.push, NTables.sizeOf] <;>
    first
      | exact Or.inl trivial
      | exact Or.inr ⟨Tbl.size_push _ _ _ _, trivial⟩

theorem NTables.Sized_push {t : NTables} {w : NNodeView} {d : UInt64} {tr : UInt32}
    (hs : t.Sized) : (t.push w d tr).1.Sized := by
  obtain ⟨h1, h2, h3⟩ := hs
  cases w <;>
    (simp only [NTables.push, NTables.Sized]
     refine ⟨?_, ?_, ?_⟩ <;>
     first | assumption | exact Tbl.Sized_push (by assumption))

theorem NTables.count_push {t : NTables} {w : NNodeView} {d : UInt64} {tr : UInt32} :
    (t.push w d tr).1.count = t.count + 1 := by
  cases w <;> simp [NTables.push, NTables.count, Tbl.size_push] <;> omega

theorem NTables.derAt_congr {t t' : NTables} {i : NIdx} {v : NNodeView}
    (h : t.get i = some v)
    (han : ∀ n, n < t.anons.size → t'.anons.derAt n = t.anons.derAt n)
    (hst : ∀ n, n < t.strs.size → t'.strs.derAt n = t.strs.derAt n)
    (hnu : ∀ n, n < t.nums.size → t'.nums.derAt n = t.nums.derAt n) :
    t'.derAt i = t.derAt i := by
  simp only [NTables.get] at h
  simp only [NTables.derAt]
  tag_cases h
  · exact han _ (Tbl.lt_of_map h)
  · exact hst _ (Tbl.lt_of_map h)
  · exact hnu _ (Tbl.lt_of_map h)
  · simp at h

theorem NTables.derAt_push_of_get {t : NTables} {w : NNodeView} {d : UInt64}
    {tr : UInt32} {i : NIdx} {v : NNodeView} (hs : t.Sized) (h : t.get i = some v) :
    (t.push w d tr).1.derAt i = t.derAt i := by
  obtain ⟨h1, h2, h3⟩ := hs
  cases w <;>
    refine NTables.derAt_congr h ?_ ?_ ?_ <;>
    intro n hn <;> simp only [NTables.push] <;>
    first | rfl | exact Tbl.derAt_push_of_lt (by assumption) hn

theorem NTables.derAt_push_new {t : NTables} {w : NNodeView} {d : UInt64}
    {tr : UInt32} (hs : t.Sized) (htr : tr.toNat < 2)
    (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.derAt (t.push w d tr).2 = d := by
  have htag := NTables.push_tag (t := t) (w := w) (d := d) (tr := tr) htr hcap
  have hix := NTables.push_idxNat (t := t) (w := w) (d := d) (tr := tr) htr hcap
  obtain ⟨h1, h2, h3⟩ := hs
  cases w <;>
    simp only [NNodeView.tagOf] at htag <;>
    simp only [NTables.sizeOf] at hix <;>
    simp only [NTables.derAt, htag, hix, NTag.anonymous, NTag.str, NTag.num,
      beq_self_eq_true, ite_true] <;>
    (simp only [NTables.push]; exact Tbl.derAt_push_size (by assumption))

/-- con-leche: none — arena infrastructure; appending a name to the scratch
tier keeps `NStoreWF`.  Precedent: con-leche's retired
`Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem NStore.wf_push_scr {st st' : NStore} {rk : NIdx → Nat} {w : NNodeView}
    {tb : NTables} {inew : NIdx}
    (h : NWFAt st rk) (hv : st.ViewOK w)
    (hon : st.scratchOn = true) (hon' : st'.scratchOn = true)
    (hpers : st'.pers = st.pers)
    (hpush : st.scr.push w (st.derOfView w) Idx.tierS = (tb, inew))
    (hscr : st'.scr = tb)
    (hcap : st.scr.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) (hfs : st.scr.find? w = none) :
    NStoreWF st' := by
  have htr : (Idx.tierS : UInt32).toNat < 2 := by decide
  have htb : (st.scr.push w (st.derOfView w) Idx.tierS).1 = tb := by rw [hpush]
  have hid : (st.scr.push w (st.derOfView w) Idx.tierS).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (NTables.push_spec st.scr w _ Idx.tierS htr hcap).1
  have hnp : inew.isPersistent = false := by
    show (inew.tier == 0) = false
    rw [← hid, (NTables.push_spec st.scr w _ Idx.tierS htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact NTables.push_tag htr hcap
  have hix : inew.idxNat = st.scr.sizeOf w := by
    rw [← hid]; exact NTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.scr.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact NTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.scr.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.scr.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact NTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.scr.find? u := by
    intro u; rw [← htb, ← hid]; exact NTables.find?_push
  have hdertb : ∀ i u, st.scr.get i = some u → tb.derAt i = st.scr.derAt i := by
    intro i u hi; rw [← htb]; exact NTables.derAt_push_of_get h.sizedS hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact NTables.derAt_push_new h.sizedS htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact NTables.Sized_push h.sizedS
  have hcounttb : tb.count = st.scr.count + 1 := by rw [← htb]; exact NTables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases NTables.sizeOf_push_cases (t := st.scr) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierS) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capS u
    · rw [h1]; omega
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp; rw [NStore.view_pers hp, NStore.view_pers hp, hpers]
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = tb.get i := by
    intro i hp; rw [NStore.view_scr hp hon', hscr]
  have hnew_none : st.view inew = none := by
    rw [NStore.view_scr hnp hon]; exact NTables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp]; exact hu
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp']
      exact hmonotb i u (by rwa [NStore.view_scr hp' hon] at hu)
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact Or.inl (by rwa [hviewP i hp] at hu)
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [NStore.view_scr hp' hon]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierS hp').trans (Idx.tier_eq_tierS hnp).symm)
          (h3.trans hix.symm), h4⟩
  have hpc : st'.persCount = st.persCount := by simp only [NStore.persCount, hpers]
  have hnc : st'.nodeCount = st.nodeCount + 1 := by
    simp only [NStore.nodeCount, NStore.persCount, NStore.scrCount, hpers, hscr,
      hcounttb]
    omega
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp : i.isPersistent = true
    · rw [NStore.derived_pers hp, NStore.derived_pers hp, hpers]
    · have hp' : i.isPersistent = false := by simpa using hp
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [NStore.derived_scr hp' hon', NStore.derived_scr hp' hon, hscr]
      exact hdertb i u (by rwa [NStore.view_scr hp' hon] at hu)
  have hdov : ∀ u : NNodeView, (∀ c ∈ u.children, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u :=
    fun u hu => NStore.derOfView_congr (fun c hc => hder c (hu c hc))
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.nodeCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.nodeCount else rk inew)
      = st.nodeCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, (if (st.view c).isNone = true then st.nodeCount else rk c)
      ≤ st.nodeCount := by
    intro c
    by_cases hc : (st.view c).isSome = true
    · rw [hrkold c hc]; exact Nat.le_of_lt (h.rank_lt hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨fun c => if (st.view c).isNone = true then st.nodeCount else rk c,
    { childOK := ?childOK, rankP := ?rankP, rankS := ?rankS, consP := ?consP,
      consS := ?consS, fresh := ?fresh, derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff }⟩
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv c hc
      refine ⟨hmoneS c hcs, ?_, ?_⟩
      · rw [hrkold c hcs, hrknew]; exact h.rank_lt hcs
      · intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case rankP =>
    intro i hp hi
    have hi' : (st.view i).isSome = true := by rw [← hviewP i hp]; exact hi
    rw [hrkold i hi', hpc]
    exact h.rankP i hp hi'
  case rankS =>
    intro i _ _
    have := hrkle i
    omega
  case consP =>
    intro u i
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
      exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP u i).mpr ⟨by rwa [hviewP i h2] at h1, h2⟩
  case consS =>
    intro u i
    rw [hscr, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consS u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfs] at hf
          exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case fresh =>
    intro u i hf
    rw [hscr, hfindtb u] at hf
    rw [hpers]
    by_cases hw : w = u
    · subst hw; exact hfp
    · rw [ite_eq_right hw] at hf; exact h.fresh u i hf
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv, NStore.derived_scr hnp hon', hscr, hdernew]
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact hsizedtb
  case capP => rw [hpers]; exact h.capP
  case capS => rw [hscr]; exact hcaptb
  case scrOff => intro hoff; rw [hon'] at hoff; exact absurd hoff (by simp)

/-- con-leche: none — arena infrastructure; appending a name to the
persistent tier keeps `NStoreWF`.  The scratch tier is empty here
(`scrOff`), so every handle that decodes is persistent — which is exactly
what `childOK`'s persistence conjunct needs for the new node.  Precedent:
con-leche's retired `Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem NStore.wf_push_pers {st st' : NStore} {rk : NIdx → Nat} {w : NNodeView}
    {tb : NTables} {inew : NIdx}
    (h : NWFAt st rk) (hv : st.ViewOK w)
    (hon : st.scratchOn = false) (hon' : st'.scratchOn = false)
    (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    NStoreWF st' := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have hscrE : st.scr = NTables.empty := h.scrOff hon
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (NTables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (NTables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact NTables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact NTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact NTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact NTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact NTables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact NTables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact NTables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact NTables.Sized_push h.sizedP
  have hcounttb : tb.count = st.pers.count + 1 := by rw [← htb]; exact NTables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases NTables.sizeOf_push_cases (t := st.pers) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierP) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capP u
    · rw [h1]; omega
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp; rw [NStore.view_pers hp, hpers]
  have hviewN' : ∀ i, i.isPersistent = false → st'.view i = none :=
    fun i hp => NStore.view_off hp hon'
  have hviewN : ∀ i, i.isPersistent = false → st.view i = none :=
    fun i hp => NStore.view_off hp hon
  have hallP : ∀ i u, st.view i = some u → i.isPersistent = true := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hnew_none : st.view inew = none := by
    rw [NStore.view_pers hnp]; exact NTables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    have hp := hallP i u hu
    rw [hviewP i hp]
    exact hmonotb i u (by rwa [NStore.view_pers hp] at hu)
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [NStore.view_pers hp]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp).trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewN' i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hpc : st'.persCount = st.persCount + 1 := by
    simp only [NStore.persCount, hpers, hcounttb]
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    have hp := hallP i u hu
    rw [NStore.derived_pers hp, NStore.derived_pers hp, hpers]
    exact hdertb i u (by rwa [NStore.view_pers hp] at hu)
  have hdov : ∀ u : NNodeView, (∀ c ∈ u.children, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u :=
    fun u hu => NStore.derOfView_congr (fun c hc => hder c (hu c hc))
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.persCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.persCount else rk inew)
      = st.persCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, (if (st.view c).isNone = true then st.persCount else rk c)
      ≤ st.persCount := by
    intro c
    by_cases hc : (st.view c).isSome = true
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
      rw [hrkold c hc]
      exact Nat.le_of_lt (h.rankP c (hallP c u hu) hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨fun c => if (st.view c).isNone = true then st.persCount else rk c,
    { childOK := ?childOK, rankP := ?rankP, rankS := ?rankS, consP := ?consP,
      consS := ?consS, fresh := ?fresh, derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff }⟩
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv c hc
      obtain ⟨uc, huc⟩ := Option.isSome_iff_exists.mp hcs
      have hcp : c.isPersistent = true := hallP c uc huc
      refine ⟨hmoneS c hcs, ?_, fun _ => hcp⟩
      rw [hrkold c hcs, hrknew]
      exact h.rankP c hcp hcs
  case rankP =>
    intro i _ _
    rw [hpc]
    have := hrkle i
    omega
  case rankS =>
    intro i hp hi
    rw [hviewN' i hp] at hi; exact absurd hi (by simp)
  case consP =>
    intro u i
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consS =>
    intro u i
    rw [hscr, hscrE, NTables.find?_empty]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hviewN' i h2] at h1; exact absurd h1 (by simp)
  case fresh =>
    intro u i hf
    rw [hscr, hscrE, NTables.find?_empty] at hf
    exact absurd hf (by simp)
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv, NStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro _; rw [hscr]; exact hscrE

/-- con-leche: none — arena infrastructure; `intern` preserves the name
store's invariant.  Precedent: con-leche's retired
`Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem NStore.intern_wf {st : NStore} {w : NNodeView} (h : NStoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) : NStoreWF (st.intern w).1 := by
  obtain ⟨rk, h⟩ := h
  simp only [NStore.capOK] at hcap
  simp only [NStore.intern]
  split
  · exact ⟨rk, h⟩
  · rename_i hfp
    split
    · rename_i hon
      split
      · exact ⟨rk, h⟩
      · rename_i hfs
        rw [ite_eq_left hon] at hcap
        exact NStore.wf_push_scr h hv hon hon rfl rfl rfl hcap hfp hfs
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [ite_eq_right hoff] at hcap
      exact NStore.wf_push_pers h hv hoff' hoff' rfl rfl rfl hcap hfp

/-- con-leche: none — `view` of a freshly interned name is the node that was
interned. -/
theorem NStore.intern_view_spec {st : NStore} {w : NNodeView} (h : NStoreWF st)
    (_hv : st.ViewOK w) (hcap : st.capOK w) :
    (st.intern w).1.view (st.intern w).2 = some w := by
  obtain ⟨rk, hwf⟩ := h
  simp only [NStore.capOK] at hcap
  simp only [NStore.intern]
  split
  · rename_i i heq
    exact ((hwf.consP w i).mp heq).1
  · split
    · rename_i hon
      split
      · rename_i i heq
        exact ((hwf.consS w i).mp heq).1
      · rw [ite_eq_left hon] at hcap
        have hspec := NTables.push_spec st.scr w (st.derOfView w) Idx.tierS
          (by decide) hcap
        have hp : ((st.scr.push w (st.derOfView w) Idx.tierS).2).isPersistent = false := by
          show (_ == 0) = false
          rw [hspec.2]; decide
        simp only [NStore.view]
        rw [ite_eq_right (by simp [hp]), ite_eq_left hon]
        exact hspec.1
    · rename_i hoff
      rw [ite_eq_right hoff] at hcap
      have hspec := NTables.push_spec st.pers w (st.derOfView w) Idx.tierP
        (by decide) hcap
      have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [NStore.view]
      rw [ite_eq_left hp]
      exact hspec.1

theorem NStore.view_intern_mono (st : NStore) (w : NNodeView) {i : NIdx}
    {v : NNodeView} (h : st.view i = some v) : (st.intern w).1.view i = some v := by
  simp only [NStore.intern]
  split
  · exact h
  · split
    · rename_i hon
      split
      · exact h
      · simp only [NStore.view, hon] at h ⊢
        by_cases hp : i.isPersistent = true
        · rw [ite_eq_left hp] at h ⊢; exact h
        · rw [ite_eq_right hp] at h ⊢; exact NTables.get_push_mono _ _ _ _ h
    · rename_i hoff
      simp only [NStore.view, hoff] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [ite_eq_left hp] at h ⊢; exact NTables.get_push_mono _ _ _ _ h
      · rw [ite_eq_right hp] at h ⊢; exact h

theorem NStore.nodeCount_intern_le (st : NStore) (w : NNodeView) :
    st.nodeCount ≤ (st.intern w).1.nodeCount := by
  simp only [NStore.intern]
  split
  · exact Nat.le_refl _
  · split
    · split
      · exact Nat.le_refl _
      · simp only [NStore.nodeCount, NStore.persCount, NStore.scrCount,
          NTables.count_push]
        omega
    · simp only [NStore.nodeCount, NStore.persCount, NStore.scrCount,
        NTables.count_push]
      omega

theorem denoteNAux_store_mono {st st' : NStore}
    (hv : ∀ i v, st.view i = some v → st'.view i = some v) :
    ∀ (f : Nat) (i : NIdx) (x : ConLeche.Name),
      denoteNAux st f i = some x → denoteNAux st' f i = some x := by
  intro f
  induction f with
  | zero => intro i x hd; simp [denoteNAux] at hd
  | succ k ih =>
    intro i x hd
    simp only [denoteNAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hvv, hd⟩ := hd
    refine ⟨v, hv i v hvv, ?_⟩
    cases v with
    | anonymous => exact hd
    | str p sv =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih p q hq, he⟩
    | num p k' =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih p q hq, he⟩

/-- con-leche: none — arena infrastructure; interning a name extends the
store.  Precedent: con-leche's retired `Verify/SimI.lean:244 Ext` (at
94a1cf78). -/
theorem NStore.intern_ext (st : NStore) (w : NNodeView) : NExt st (st.intern w).1 := by
  intro i x hd
  simp only [denoteN] at hd ⊢
  have h1 : denoteNAux st ((st.intern w).1.nodeCount + 1) i = some x :=
    denoteNAux_mono st (st.nodeCount + 1) ((st.intern w).1.nodeCount + 1) i x
      (by have := NStore.nodeCount_intern_le st w; omega) hd
  exact denoteNAux_store_mono (fun _ _ hh => NStore.view_intern_mono st w hh) _ i x h1


/-! ### The persistent tier — and the `sync` clause

**Task #97a's finding (2026-09-20), and its fix.**  `EWFAt.lchildOK` demands
that a *persistent* expression node's level child be persistent, and `intern`
appends to the persistent tier exactly when `st.scratchOn = false`.  The child
is known only to decode — `EStore.ViewOK` — and a level handle decodes against
`st.ls.scratchOn`, a **different flag**.  While `WF.lean` did not tie the two,

    st := { lss := <a level store with scratchOn := true and one scratch level u>,
            pers := .empty, scr := .empty, scratchOn := false }

satisfied `StoreWF st`, `st.ViewOK (.sort u)` and `st.capOK (.sort u)`, and
`(st.intern (.sort u)).1` then had a persistent node with a scratch level
child: `StoreWF` failed.  `EStore.intern_wf` was therefore *not provable*, and
the same hole sat under `LStore.intern_spec` (`LWFAt.nchildOK`) and
`LsStore.intern_spec` (`LsWF.lchildOK`).

The flag synchronisation *is* an invariant of the API — `empty`,
`enableScratch` and `dropScratch` set all four flags together and `intern`
touches none of them — it was simply missing from `WF.lean`.  It is now a
clause of each nested invariant (`LWFAt.sync`, `LsWF.sync`, `EWFAt.sync`, one
`scratchOn = <substore>.scratchOn` apiece), and the `…_of_sync` lemmas below
take `hsync` as an argument only so that the two push lemmas can be stated
about an arbitrary `st'`; every caller reads it off the invariant, via
`EWFAt.scratchSync` and its two siblings.  The refutation that established the
finding, `EStore.intern_wf_refuted_without_sync`, went with the hole: under the
`sync` clause its hypotheses are contradictory, so it would now be a vacuous
theorem. -/

/-- con-leche: none — the three flat equalities of the `sync` clauses: the
nesting's scratch flags move together (task #97a).  `EWFAt` states the fact
one level at a time; this is the transitive closure the push lemmas want. -/
structure EStore.ScratchSync (st : EStore) : Prop where
  ns : st.scratchOn = st.ns.scratchOn
  ls : st.scratchOn = st.ls.scratchOn
  lss : st.scratchOn = st.lss.scratchOn

/-- con-leche: none — `EWFAt`'s `sync` clause, unfolded through the nesting. -/
theorem EWFAt.scratchSync {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    st.ScratchSync := by
  have hlss : LsWF st.lss := h.lss
  obtain ⟨rkl, hl⟩ := hlss.ls
  exact { lss := h.sync, ls := h.sync.trans hlss.sync,
          ns := (h.sync.trans hlss.sync).trans hl.sync }

/-- con-leche: none — the same, off `StoreWF`. -/
theorem StoreWF.scratchSync {st : EStore} (h : StoreWF st) : st.ScratchSync := by
  obtain ⟨rk, h⟩ := h; exact h.scratchSync

/-- con-leche: none — arena infrastructure; appending to the persistent tier
keeps `StoreWF`.  `hsync` is the missing clause.  Precedent: con-leche's
retired `Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem EStore.wf_push_pers {st st' : EStore} {rk : EIdx → Nat} {w : ENodeView}
    {tb : ETables} {inew : EIdx}
    (h : EWFAt st rk) (hv : st.ViewOK w) (hsync : st.ScratchSync)
    (hon : st.scratchOn = false) (hon' : st'.scratchOn = false)
    (hlss : st'.lss = st.lss) (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    StoreWF st' ∧ st'.view inew = some w ∧ inew.isPersistent = true := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have hscrE : st.scr = ETables.empty := h.scrOff hon
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (ETables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (ETables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact ETables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact ETables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact ETables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact ETables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact ETables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact ETables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact ETables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact ETables.Sized_push h.sizedP
  have hcounttb : tb.count = st.pers.count + 1 := by rw [← htb]; exact ETables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases ETables.sizeOf_push_cases (t := st.pers) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierP) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capP u
    · rw [h1]; omega
  -- the sub-stores are untouched, and their scratch tiers are off too
  have hns : st'.ns = st.ns := by simp only [EStore.ns, hlss]
  have hls : st'.ls = st.ls := by simp only [EStore.ls, hlss]
  have hnsoff : st.ns.scratchOn = false := by rw [← hsync.ns]; exact hon
  have hlsoff : st.ls.scratchOn = false := by rw [← hsync.ls]; exact hon
  have hlssoff : st.lss.scratchOn = false := by rw [← hsync.lss]; exact hon
  have hallPN : ∀ c : NIdx, (st.ns.view c).isSome = true → c.isPersistent = true := by
    intro c hc
    by_cases hp : c.isPersistent = true
    · exact hp
    · rw [NStore.view_off (by simpa using hp) hnsoff] at hc; exact absurd hc (by simp)
  have hallPL : ∀ c : LIdx, (st.ls.view c).isSome = true → c.isPersistent = true := by
    intro c hc
    by_cases hp : c.isPersistent = true
    · exact hp
    · rw [LStore.view_off (by simpa using hp) hlsoff] at hc; exact absurd hc (by simp)
  have hallPLs : ∀ c : LsIdx, (st.lss.view c).isSome = true → c.isPersistent = true := by
    intro c hc
    by_cases hp : c.isPersistent = true
    · exact hp
    · rw [LsStore.view_off (by simpa using hp) hlssoff] at hc; exact absurd hc (by simp)
  -- the two tiers, as `view` sees them
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp; rw [EStore.view_pers hp, hpers]
  have hviewN' : ∀ i, i.isPersistent = false → st'.view i = none :=
    fun i hp => EStore.view_off hp hon'
  have hviewN : ∀ i, i.isPersistent = false → st.view i = none :=
    fun i hp => EStore.view_off hp hon
  have hallP : ∀ i u, st.view i = some u → i.isPersistent = true := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hnew_none : st.view inew = none := by
    rw [EStore.view_pers hnp]; exact ETables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    have hp := hallP i u hu
    rw [hviewP i hp]
    exact hmonotb i u (by rwa [EStore.view_pers hp] at hu)
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [EStore.view_pers hp]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp).trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewN' i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hpc : st'.persCount = st.persCount + 1 := by
    simp only [EStore.persCount, hpers, hcounttb]
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    have hp := hallP i u hu
    rw [EStore.derived_pers hp, EStore.derived_pers hp, hpers]
    exact hdertb i u (by rwa [EStore.view_pers hp] at hu)
  have hdov : ∀ u : ENodeView, (∀ c ∈ u.echildren, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u := by
    intro u hu
    refine EStore.derOfView_congr (fun c hc => hder c (hu c hc)) ?_ ?_ ?_ <;>
      intro c _ <;>
      simp only [EStore.nder, EStore.lder, EStore.lsder, hns, hls, hlss]
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.persCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.persCount else rk inew)
      = st.persCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, (if (st.view c).isNone = true then st.persCount else rk c)
      ≤ st.persCount := by
    intro c
    by_cases hc : (st.view c).isSome = true
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
      rw [hrkold c hc]
      exact Nat.le_of_lt (h.rankP c (hallP c u hu) hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨?wf, by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
  case wf =>
  refine ⟨fun c => if (st.view c).isNone = true then st.persCount else rk c,
    { lss := ?lss, childOK := ?childOK, nchildOK := ?nchildOK,
      lchildOK := ?lchildOK, lschildOK := ?lschildOK,
      rankP := ?rankP, rankS := ?rankS, consP := ?consP, consS := ?consS,
      fresh := ?fresh, derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff,
      sync := by rw [hon', hlss, ← h.sync, hon] }⟩
  case lss => rw [hlss]; exact h.lss
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv.expr c hc
      obtain ⟨uc, huc⟩ := Option.isSome_iff_exists.mp hcs
      have hcp : c.isPersistent = true := hallP c uc huc
      refine ⟨hmoneS c hcs, ?_, fun _ => hcp⟩
      rw [hrkold c hcs, hrknew]
      exact h.rankP c hcp hcs
  case nchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hns]; exact h.nchildOK i u hi' c hc
    · exact ⟨by rw [hns]; exact hv.nm c hc, fun _ => hallPN c (hv.nm c hc)⟩
  case lchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hls]; exact h.lchildOK i u hi' c hc
    · exact ⟨by rw [hls]; exact hv.lvl c hc, fun _ => hallPL c (hv.lvl c hc)⟩
  case lschildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hlss]; exact h.lschildOK i u hi' c hc
    · exact ⟨by rw [hlss]; exact hv.lst c hc, fun _ => hallPLs c (hv.lst c hc)⟩
  case rankP =>
    intro i _ _
    rw [hpc]
    have := hrkle i
    omega
  case rankS =>
    intro i hp hi
    rw [hviewN' i hp] at hi; exact absurd hi (by simp)
  case consP =>
    intro u i
    simp only [EStore.persFind?]
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; simp only [EStore.persFind?] at hf; rw [hfp] at hf
          exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consS =>
    intro u i
    simp only [EStore.scrFind?]
    rw [hscr, hscrE, ETables.find?_empty]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hviewN' i h2] at h1; exact absurd h1 (by simp)
  case fresh =>
    intro u i hf
    simp only [EStore.persFind?, EStore.scrFind?] at hf ⊢
    rw [hscr, hscrE, ETables.find?_empty] at hf
    exact absurd hf (by simp)
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.expr, EStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro _; rw [hscr]; exact hscrE

/-- con-leche: none — arena infrastructure; `intern` preserves the store
invariant and its handle decodes to the node interned.  The flag
synchronisation the persistent case needs is `EWFAt.sync` (task #97a). -/
theorem EStore.intern_wf_view_of_sync {st : EStore} {w : ENodeView} (h : StoreWF st)
    (hsync : st.ScratchSync) (hv : st.ViewOK w) (hcap : st.capOK w) :
    StoreWF (st.intern w).1 ∧ (st.intern w).1.view (st.intern w).2 = some w := by
  obtain ⟨rk, h⟩ := h
  simp only [EStore.capOK] at hcap
  simp only [EStore.intern, EStore.persFindMaybe_eq ⟨rk, h⟩]
  split
  · rename_i i hi
    exact ⟨⟨rk, h⟩, ((h.consP w i).mp hi).1⟩
  · rename_i hfp
    split
    · rename_i hon
      split
      · rename_i i hi
        exact ⟨⟨rk, h⟩, ((h.consS w i).mp hi).1⟩
      · rename_i hfs
        rw [ite_eq_left hon] at hcap
        obtain ⟨hwf, hvw, _⟩ := EStore.wf_push_scr
          (st' := { st with scr := (st.scr.push w (st.derOfView w) Idx.tierS).1 })
          (tb := (st.scr.push w (st.derOfView w) Idx.tierS).1)
          (inew := (st.scr.push w (st.derOfView w) Idx.tierS).2)
          h hv hon hon rfl rfl rfl rfl hcap hfp hfs
        exact ⟨hwf, hvw⟩
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [ite_eq_right hoff] at hcap
      obtain ⟨hwf, hvw, _⟩ := EStore.wf_push_pers
        (st' := { st with pers := (st.pers.push w (st.derOfView w) Idx.tierP).1 })
        (tb := (st.pers.push w (st.derOfView w) Idx.tierP).1)
        (inew := (st.pers.push w (st.derOfView w) Idx.tierP).2)
        h hv hsync hoff' hoff' rfl rfl rfl rfl hcap hfp
      exact ⟨hwf, hvw⟩

/-- con-leche: none — arena infrastructure; `view` of a freshly interned node
is the node that was interned. -/
theorem EStore.intern_view_spec {st : EStore} {w : ENodeView} (h : StoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    (st.intern w).1.view (st.intern w).2 = some w :=
  (EStore.intern_wf_view_of_sync h h.scratchSync hv hcap).2

theorem EStore.intern_wf_of_sync {st : EStore} {w : ENodeView} (h : StoreWF st)
    (hsync : st.ScratchSync) (hv : st.ViewOK w) (hcap : st.capOK w) :
    StoreWF (st.intern w).1 :=
  (EStore.intern_wf_view_of_sync h hsync hv hcap).1

/-! ## `intern` on the level store -/

/-- con-leche: none — the constructor tag a level node view lands under. -/
def LNodeView.tagOf : LNodeView → UInt32
  | .zero => LTag.zero
  | .succ _ => LTag.succ
  | .max _ _ => LTag.max
  | .imax _ _ => LTag.imax
  | .param _ => LTag.param

theorem LTables.get_inv {t t' : LTables} {Q : UInt32 → Nat → LNodeView → Prop}
    {i : LIdx} {v : LNodeView}
    (hze : ∀ n a, t'.zeros.node? n = some a →
      t.zeros.node? n = some a ∨ Q LTag.zero n .zero)
    (hsu : ∀ n a, t'.succs.node? n = some a →
      t.succs.node? n = some a ∨ Q LTag.succ n (.succ a.u))
    (hma : ∀ n a, t'.maxs.node? n = some a →
      t.maxs.node? n = some a ∨ Q LTag.max n (.max a.u a.v))
    (him : ∀ n a, t'.imaxs.node? n = some a →
      t.imaxs.node? n = some a ∨ Q LTag.imax n (.imax a.u a.v))
    (hpa : ∀ n a, t'.params.node? n = some a →
      t.params.node? n = some a ∨ Q LTag.param n (.param a.n))
    (h : t'.get i = some v) : t.get i = some v ∨ Q i.tag i.idxNat v := by
  simp only [LTables.get] at h ⊢
  tag_cases h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hze _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hsu _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hma _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (him _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hpa _) h
  · simp at h

theorem LTables.get_push_inv {t : LTables} {w : LNodeView} {d : LDer} {tr : UInt32}
    {i : LIdx} {v : LNodeView} (h : (t.push w d tr).1.get i = some v) :
    t.get i = some v ∨ (i.tag = w.tagOf ∧ i.idxNat = t.sizeOf w ∧ v = w) := by
  refine LTables.get_inv (Q := fun tg n v' => tg = w.tagOf ∧ n = t.sizeOf w ∧ v' = w)
    ?_ ?_ ?_ ?_ ?_ h <;>
    intro n a ha <;> cases w <;>
    simp only [LTables.push] at ha <;>
    first
      | exact Or.inl ha
      | (rw [Tbl.node?_push_eq] at ha
         split at ha
         · refine Or.inr ⟨rfl, by simp only [LTables.sizeOf]; assumption, ?_⟩
           simp only [Option.some.injEq] at ha
           first | (subst ha; rfl) | rfl
         · exact Or.inl ha)

theorem LTables.get_eq_none_of_size {t : LTables} {w : LNodeView} {i : LIdx}
    (htg : i.tag = w.tagOf) (hix : i.idxNat = t.sizeOf w) : t.get i = none := by
  cases w <;>
    simp only [LNodeView.tagOf] at htg <;>
    simp only [LTables.sizeOf] at hix <;>
    simp [LTables.get, htg, hix, LTag.zero, LTag.succ, LTag.max, LTag.imax,
      LTag.param, Tbl.node?_size]

theorem LTables.get_mono {t t' : LTables}
    (hze : ∀ n a, t.zeros.node? n = some a → t'.zeros.node? n = some a)
    (hsu : ∀ n a, t.succs.node? n = some a → t'.succs.node? n = some a)
    (hma : ∀ n a, t.maxs.node? n = some a → t'.maxs.node? n = some a)
    (him : ∀ n a, t.imaxs.node? n = some a → t'.imaxs.node? n = some a)
    (hpa : ∀ n a, t.params.node? n = some a → t'.params.node? n = some a)
    {i : LIdx} {v : LNodeView} (h : t.get i = some v) : t'.get i = some v := by
  simp only [LTables.get] at h ⊢
  tag_cases h
  · exact Option.map_mono (hze _) h
  · exact Option.map_mono (hsu _) h
  · exact Option.map_mono (hma _) h
  · exact Option.map_mono (him _) h
  · exact Option.map_mono (hpa _) h
  · simp at h

theorem LTables.get_push_mono (t : LTables) (w : LNodeView) (d : LDer)
    (tr : UInt32) {i : LIdx} {v : LNodeView} (h : t.get i = some v) :
    (t.push w d tr).1.get i = some v := by
  cases w <;>
    refine LTables.get_mono ?_ ?_ ?_ ?_ ?_ h <;>
    intro n a ha <;> simp only [LTables.push] <;>
    first | exact ha | exact Tbl.node?_push ha

theorem LTables.push_spec (t : LTables) (w : LNodeView) (d : LDer) (tr : UInt32)
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.get (t.push w d tr).2 = some w ∧
      (t.push w d tr).2.tier = tr := by
  simp only [LTables.sizeOf] at hcap
  cases w with
  | zero =>
    have htg : (LTag.zero : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [LTables.push, LTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [LTag.zero, Tbl.node?_push_new]
    · simp only [LTables.push, Idx.tier_mk _ _ _ htg htr hn]
  | succ u =>
    have htg : (LTag.succ : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [LTables.push, LTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [LTag.zero, LTag.succ, Tbl.node?_push_new]
    · simp only [LTables.push, Idx.tier_mk _ _ _ htg htr hn]
  | max u v =>
    have htg : (LTag.max : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [LTables.push, LTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [LTag.zero, LTag.succ, LTag.max, Tbl.node?_push_new]
    · simp only [LTables.push, Idx.tier_mk _ _ _ htg htr hn]
  | imax u v =>
    have htg : (LTag.imax : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [LTables.push, LTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [LTag.zero, LTag.succ, LTag.max, LTag.imax, Tbl.node?_push_new]
    · simp only [LTables.push, Idx.tier_mk _ _ _ htg htr hn]
  | param n =>
    have htg : (LTag.param : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [LTables.push, LTables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [LTag.zero, LTag.succ, LTag.max, LTag.imax, LTag.param,
        Tbl.node?_push_new]
    · simp only [LTables.push, Idx.tier_mk _ _ _ htg htr hn]

theorem LTables.push_tag {t : LTables} {w : LNodeView} {d : LDer} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.tag = w.tagOf := by
  have hn : ((UInt32.ofNat (t.sizeOf w)).toNat) < Idx.idxCap := by
    rw [Idx.idxCap] at hcap ⊢; simp; omega
  cases w <;>
    simp only [LTables.push, LNodeView.tagOf, LTables.sizeOf] at * <;>
    exact Idx.tag_mk _ _ _ (by decide) htr hn

theorem LTables.push_idxNat {t : LTables} {w : LNodeView} {d : LDer} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.idxNat = t.sizeOf w := by
  cases w <;>
    simp only [LTables.push, LTables.sizeOf] at * <;>
    exact Idx.idxNat_mk _ _ _ (by decide) htr hcap

theorem LTables.find?_push {t : LTables} {w v : LNodeView} {d : LDer} {tr : UInt32} :
    (t.push w d tr).1.find? v =
      if w = v then some (t.push w d tr).2 else t.find? v := by
  cases w <;> cases v <;>
    simp only [LTables.push, LTables.find?, Tbl.find?_push, beq_iff_eq,
      SuccNode.mk.injEq, BinLNode.mk.injEq, ParamNode.mk.injEq,
      LNodeView.succ.injEq, LNodeView.max.injEq, LNodeView.imax.injEq,
      LNodeView.param.injEq, beq_self_eq_true, reduceCtorEq, ite_false,
      ite_true] <;>
    rfl

theorem LTables.sizeOf_push_cases {t : LTables} {w v : LNodeView} {d : LDer}
    {tr : UInt32} :
    (t.push w d tr).1.sizeOf v = t.sizeOf v ∨
      ((t.push w d tr).1.sizeOf v = t.sizeOf w + 1 ∧ t.sizeOf v = t.sizeOf w) := by
  cases w <;> cases v <;>
    simp only [LTables.push, LTables.sizeOf] <;>
    first
      | exact Or.inl trivial
      | exact Or.inr ⟨Tbl.size_push _ _ _ _, trivial⟩

theorem LTables.Sized_push {t : LTables} {w : LNodeView} {d : LDer} {tr : UInt32}
    (hs : t.Sized) : (t.push w d tr).1.Sized := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  cases w <;>
    (simp only [LTables.push, LTables.Sized]
     refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
     first | assumption | exact Tbl.Sized_push (by assumption))

theorem LTables.count_push {t : LTables} {w : LNodeView} {d : LDer} {tr : UInt32} :
    (t.push w d tr).1.count = t.count + 1 := by
  cases w <;> simp [LTables.push, LTables.count, Tbl.size_push] <;> omega

theorem LTables.derAt_congr {t t' : LTables} {i : LIdx} {v : LNodeView}
    (h : t.get i = some v)
    (hze : ∀ n, n < t.zeros.size → t'.zeros.derAt n = t.zeros.derAt n)
    (hsu : ∀ n, n < t.succs.size → t'.succs.derAt n = t.succs.derAt n)
    (hma : ∀ n, n < t.maxs.size → t'.maxs.derAt n = t.maxs.derAt n)
    (him : ∀ n, n < t.imaxs.size → t'.imaxs.derAt n = t.imaxs.derAt n)
    (hpa : ∀ n, n < t.params.size → t'.params.derAt n = t.params.derAt n) :
    t'.derAt i = t.derAt i := by
  simp only [LTables.get] at h
  simp only [LTables.derAt]
  tag_cases h
  · exact hze _ (Tbl.lt_of_map h)
  · exact hsu _ (Tbl.lt_of_map h)
  · exact hma _ (Tbl.lt_of_map h)
  · exact him _ (Tbl.lt_of_map h)
  · exact hpa _ (Tbl.lt_of_map h)
  · simp at h

theorem LTables.derAt_push_of_get {t : LTables} {w : LNodeView} {d : LDer}
    {tr : UInt32} {i : LIdx} {v : LNodeView} (hs : t.Sized) (h : t.get i = some v) :
    (t.push w d tr).1.derAt i = t.derAt i := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  cases w <;>
    refine LTables.derAt_congr h ?_ ?_ ?_ ?_ ?_ <;>
    intro n hn <;> simp only [LTables.push] <;>
    first | rfl | exact Tbl.derAt_push_of_lt (by assumption) hn

theorem LTables.derAt_push_new {t : LTables} {w : LNodeView} {d : LDer}
    {tr : UInt32} (hs : t.Sized) (htr : tr.toNat < 2)
    (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.derAt (t.push w d tr).2 = d := by
  have htag := LTables.push_tag (t := t) (w := w) (d := d) (tr := tr) htr hcap
  have hix := LTables.push_idxNat (t := t) (w := w) (d := d) (tr := tr) htr hcap
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  cases w <;>
    simp only [LNodeView.tagOf] at htag <;>
    simp only [LTables.sizeOf] at hix <;>
    simp only [LTables.derAt, htag, hix, LTag.zero, LTag.succ, LTag.max,
      LTag.imax, LTag.param, beq_self_eq_true, ite_true] <;>
    (simp only [LTables.push]; exact Tbl.derAt_push_size (by assumption))

/-- con-leche: none — `LWFAt`'s `sync` clause, named (task #97a). -/
def LStore.ScratchSync (st : LStore) : Prop := st.scratchOn = st.ns.scratchOn

/-- con-leche: none — the same, off `LStoreWF`. -/
theorem LStoreWF.scratchSync {st : LStore} (h : LStoreWF st) : st.ScratchSync := by
  obtain ⟨rk, h⟩ := h; exact h.sync

theorem LStore.wf_push_scr {st st' : LStore} {rk : LIdx → Nat} {w : LNodeView}
    {tb : LTables} {inew : LIdx}
    (h : LWFAt st rk) (hv : st.ViewOK w)
    (hon : st.scratchOn = true) (hon' : st'.scratchOn = true)
    (hns : st'.ns = st.ns) (hpers : st'.pers = st.pers)
    (hpush : st.scr.push w (st.derOfView w) Idx.tierS = (tb, inew))
    (hscr : st'.scr = tb)
    (hcap : st.scr.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) (hfs : st.scr.find? w = none) :
    LStoreWF st' := by
  have htr : (Idx.tierS : UInt32).toNat < 2 := by decide
  have htb : (st.scr.push w (st.derOfView w) Idx.tierS).1 = tb := by rw [hpush]
  have hid : (st.scr.push w (st.derOfView w) Idx.tierS).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (LTables.push_spec st.scr w _ Idx.tierS htr hcap).1
  have hnp : inew.isPersistent = false := by
    show (inew.tier == 0) = false
    rw [← hid, (LTables.push_spec st.scr w _ Idx.tierS htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact LTables.push_tag htr hcap
  have hix : inew.idxNat = st.scr.sizeOf w := by
    rw [← hid]; exact LTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.scr.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact LTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.scr.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.scr.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact LTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.scr.find? u := by
    intro u; rw [← htb, ← hid]; exact LTables.find?_push
  have hdertb : ∀ i u, st.scr.get i = some u → tb.derAt i = st.scr.derAt i := by
    intro i u hi; rw [← htb]; exact LTables.derAt_push_of_get h.sizedS hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact LTables.derAt_push_new h.sizedS htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact LTables.Sized_push h.sizedS
  have hcounttb : tb.count = st.scr.count + 1 := by rw [← htb]; exact LTables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases LTables.sizeOf_push_cases (t := st.scr) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierS) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capS u
    · rw [h1]; omega
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp; rw [LStore.view_pers hp, LStore.view_pers hp, hpers]
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = tb.get i := by
    intro i hp; rw [LStore.view_scr hp hon', hscr]
  have hnew_none : st.view inew = none := by
    rw [LStore.view_scr hnp hon]; exact LTables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp]; exact hu
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp']
      exact hmonotb i u (by rwa [LStore.view_scr hp' hon] at hu)
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact Or.inl (by rwa [hviewP i hp] at hu)
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [LStore.view_scr hp' hon]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierS hp').trans (Idx.tier_eq_tierS hnp).symm)
          (h3.trans hix.symm), h4⟩
  have hpc : st'.persCount = st.persCount := by simp only [LStore.persCount, hpers]
  have hnc : st'.nodeCount = st.nodeCount + 1 := by
    simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount, hpers, hscr,
      hcounttb]
    omega
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp : i.isPersistent = true
    · rw [LStore.derived_pers hp, LStore.derived_pers hp, hpers]
    · have hp' : i.isPersistent = false := by simpa using hp
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [LStore.derived_scr hp' hon', LStore.derived_scr hp' hon, hscr]
      exact hdertb i u (by rwa [LStore.view_scr hp' hon] at hu)
  have hdov : ∀ u : LNodeView, (∀ c ∈ u.lchildren, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u :=
    fun u hu => LStore.derOfView_congr (fun c hc => hder c (hu c hc))
      (fun c _ => by rw [hns])
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.nodeCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.nodeCount else rk inew)
      = st.nodeCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, (if (st.view c).isNone = true then st.nodeCount else rk c)
      ≤ st.nodeCount := by
    intro c
    by_cases hc : (st.view c).isSome = true
    · rw [hrkold c hc]; exact Nat.le_of_lt (h.rank_lt hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨fun c => if (st.view c).isNone = true then st.nodeCount else rk c,
    { ns := by rw [hns]; exact h.ns, childOK := ?childOK, nchildOK := ?nchildOK,
      rankP := ?rankP, rankS := ?rankS, consP := ?consP, consS := ?consS,
      fresh := ?fresh, derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff,
      sync := by rw [hon', hns, ← h.sync, hon] }⟩
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv.lvl c hc
      refine ⟨hmoneS c hcs, ?_, ?_⟩
      · rw [hrkold c hcs, hrknew]; exact h.rank_lt hcs
      · intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case nchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hns]; exact h.nchildOK i u hi' c hc
    · refine ⟨by rw [hns]; exact hv.nm c hc, ?_⟩
      intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case rankP =>
    intro i hp hi
    have hi' : (st.view i).isSome = true := by rw [← hviewP i hp]; exact hi
    rw [hrkold i hi', hpc]
    exact h.rankP i hp hi'
  case rankS =>
    intro i _ _
    have := hrkle i
    omega
  case consP =>
    intro u i
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
      exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP u i).mpr ⟨by rwa [hviewP i h2] at h1, h2⟩
  case consS =>
    intro u i
    rw [hscr, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consS u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfs] at hf
          exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case fresh =>
    intro u i hf
    rw [hscr, hfindtb u] at hf
    rw [hpers]
    by_cases hw : w = u
    · subst hw; exact hfp
    · rw [ite_eq_right hw] at hf; exact h.fresh u i hf
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.lvl, LStore.derived_scr hnp hon', hscr, hdernew]
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact hsizedtb
  case capP => rw [hpers]; exact h.capP
  case capS => rw [hscr]; exact hcaptb
  case scrOff => intro hoff; rw [hon'] at hoff; exact absurd hoff (by simp)

theorem LStore.wf_push_pers {st st' : LStore} {rk : LIdx → Nat} {w : LNodeView}
    {tb : LTables} {inew : LIdx}
    (h : LWFAt st rk) (hv : st.ViewOK w) (hsync : st.ScratchSync)
    (hon : st.scratchOn = false) (hon' : st'.scratchOn = false)
    (hns : st'.ns = st.ns) (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    LStoreWF st' := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have hscrE : st.scr = LTables.empty := h.scrOff hon
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (LTables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (LTables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact LTables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact LTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact LTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact LTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact LTables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact LTables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact LTables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact LTables.Sized_push h.sizedP
  have hcounttb : tb.count = st.pers.count + 1 := by rw [← htb]; exact LTables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases LTables.sizeOf_push_cases (t := st.pers) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierP) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capP u
    · rw [h1]; omega
  have hnsoff : st.ns.scratchOn = false := by
    rw [← hsync]; exact hon
  have hallPN : ∀ c : NIdx, (st.ns.view c).isSome = true → c.isPersistent = true := by
    intro c hc
    by_cases hp : c.isPersistent = true
    · exact hp
    · rw [NStore.view_off (by simpa using hp) hnsoff] at hc; exact absurd hc (by simp)
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp; rw [LStore.view_pers hp, hpers]
  have hviewN' : ∀ i, i.isPersistent = false → st'.view i = none :=
    fun i hp => LStore.view_off hp hon'
  have hviewN : ∀ i, i.isPersistent = false → st.view i = none :=
    fun i hp => LStore.view_off hp hon
  have hallP : ∀ i u, st.view i = some u → i.isPersistent = true := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hnew_none : st.view inew = none := by
    rw [LStore.view_pers hnp]; exact LTables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    have hp := hallP i u hu
    rw [hviewP i hp]
    exact hmonotb i u (by rwa [LStore.view_pers hp] at hu)
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [LStore.view_pers hp]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp).trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewN' i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hpc : st'.persCount = st.persCount + 1 := by
    simp only [LStore.persCount, hpers, hcounttb]
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    have hp := hallP i u hu
    rw [LStore.derived_pers hp, LStore.derived_pers hp, hpers]
    exact hdertb i u (by rwa [LStore.view_pers hp] at hu)
  have hdov : ∀ u : LNodeView, (∀ c ∈ u.lchildren, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u :=
    fun u hu => LStore.derOfView_congr (fun c hc => hder c (hu c hc))
      (fun c _ => by rw [hns])
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.persCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.persCount else rk inew)
      = st.persCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, (if (st.view c).isNone = true then st.persCount else rk c)
      ≤ st.persCount := by
    intro c
    by_cases hc : (st.view c).isSome = true
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
      rw [hrkold c hc]
      exact Nat.le_of_lt (h.rankP c (hallP c u hu) hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨fun c => if (st.view c).isNone = true then st.persCount else rk c,
    { ns := by rw [hns]; exact h.ns, childOK := ?childOK, nchildOK := ?nchildOK,
      rankP := ?rankP, rankS := ?rankS, consP := ?consP, consS := ?consS,
      fresh := ?fresh, derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff,
      sync := by rw [hon', hns, ← h.sync, hon] }⟩
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv.lvl c hc
      obtain ⟨uc, huc⟩ := Option.isSome_iff_exists.mp hcs
      have hcp : c.isPersistent = true := hallP c uc huc
      refine ⟨hmoneS c hcs, ?_, fun _ => hcp⟩
      rw [hrkold c hcs, hrknew]
      exact h.rankP c hcp hcs
  case nchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hns]; exact h.nchildOK i u hi' c hc
    · exact ⟨by rw [hns]; exact hv.nm c hc, fun _ => hallPN c (hv.nm c hc)⟩
  case rankP =>
    intro i _ _
    rw [hpc]
    have := hrkle i
    omega
  case rankS =>
    intro i hp hi
    rw [hviewN' i hp] at hi; exact absurd hi (by simp)
  case consP =>
    intro u i
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consS =>
    intro u i
    rw [hscr, hscrE, LTables.find?_empty]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hviewN' i h2] at h1; exact absurd h1 (by simp)
  case fresh =>
    intro u i hf
    rw [hscr, hscrE, LTables.find?_empty] at hf
    exact absurd hf (by simp)
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.lvl, LStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro _; rw [hscr]; exact hscrE

theorem LStore.intern_wf_of_sync {st : LStore} {w : LNodeView} (h : LStoreWF st)
    (hsync : st.ScratchSync) (hv : st.ViewOK w) (hcap : st.capOK w) :
    LStoreWF (st.intern w).1 := by
  obtain ⟨rk, h⟩ := h
  simp only [LStore.capOK] at hcap
  simp only [LStore.intern]
  split
  · exact ⟨rk, h⟩
  · rename_i hfp
    split
    · rename_i hon
      split
      · exact ⟨rk, h⟩
      · rename_i hfs
        rw [ite_eq_left hon] at hcap
        exact LStore.wf_push_scr h hv hon hon rfl rfl rfl rfl hcap hfp hfs
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [ite_eq_right hoff] at hcap
      exact LStore.wf_push_pers h hv hsync hoff' hoff' rfl rfl rfl rfl hcap hfp

theorem LStore.intern_view_spec {st : LStore} {w : LNodeView} (h : LStoreWF st)
    (_hv : st.ViewOK w) (hcap : st.capOK w) :
    (st.intern w).1.view (st.intern w).2 = some w := by
  obtain ⟨rk, hwf⟩ := h
  simp only [LStore.capOK] at hcap
  simp only [LStore.intern]
  split
  · rename_i i heq
    exact ((hwf.consP w i).mp heq).1
  · split
    · rename_i hon
      split
      · rename_i i heq
        exact ((hwf.consS w i).mp heq).1
      · rw [ite_eq_left hon] at hcap
        have hspec := LTables.push_spec st.scr w (st.derOfView w) Idx.tierS
          (by decide) hcap
        have hp : ((st.scr.push w (st.derOfView w) Idx.tierS).2).isPersistent = false := by
          show (_ == 0) = false
          rw [hspec.2]; decide
        simp only [LStore.view]
        rw [ite_eq_right (by simp [hp]), ite_eq_left hon]
        exact hspec.1
    · rename_i hoff
      rw [ite_eq_right hoff] at hcap
      have hspec := LTables.push_spec st.pers w (st.derOfView w) Idx.tierP
        (by decide) hcap
      have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [LStore.view]
      rw [ite_eq_left hp]
      exact hspec.1

theorem LStore.ns_intern (st : LStore) (w : LNodeView) :
    (st.intern w).1.ns = st.ns := by
  simp only [LStore.intern]
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

theorem LStore.view_intern_mono (st : LStore) (w : LNodeView) {i : LIdx}
    {v : LNodeView} (h : st.view i = some v) : (st.intern w).1.view i = some v := by
  simp only [LStore.intern]
  split
  · exact h
  · split
    · rename_i hon
      split
      · exact h
      · simp only [LStore.view, hon] at h ⊢
        by_cases hp : i.isPersistent = true
        · rw [ite_eq_left hp] at h ⊢; exact h
        · rw [ite_eq_right hp] at h ⊢; exact LTables.get_push_mono _ _ _ _ h
    · rename_i hoff
      simp only [LStore.view, hoff] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [ite_eq_left hp] at h ⊢; exact LTables.get_push_mono _ _ _ _ h
      · rw [ite_eq_right hp] at h ⊢; exact h

theorem LStore.nodeCount_intern_le (st : LStore) (w : LNodeView) :
    st.nodeCount ≤ (st.intern w).1.nodeCount := by
  simp only [LStore.intern]
  split
  · exact Nat.le_refl _
  · split
    · split
      · exact Nat.le_refl _
      · simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount,
          LTables.count_push]
        omega
    · simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount,
        LTables.count_push]
      omega

theorem denoteLAux_store_mono {st st' : LStore}
    (hv : ∀ i v, st.view i = some v → st'.view i = some v) (hns : st'.ns = st.ns) :
    ∀ (f : Nat) (i : LIdx) (x : Level),
      denoteLAux st f i = some x → denoteLAux st' f i = some x := by
  intro f
  induction f with
  | zero => intro i x hd; simp [denoteLAux] at hd
  | succ k ih =>
    intro i x hd
    simp only [denoteLAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hvv, hd⟩ := hd
    refine ⟨v, hv i v hvv, ?_⟩
    cases v with
    | zero => exact hd
    | param n => rw [hns]; exact hd
    | succ u =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih u q hq, he⟩
    | max u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ha, ih w b hb, he⟩
    | imax u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ha, ih w b hb, he⟩

/-- con-leche: none — arena infrastructure; interning a level extends the
store.  Precedent: con-leche's retired `Verify/SimI.lean:244 Ext` (at
94a1cf78). -/
theorem LStore.intern_ext (st : LStore) (w : LNodeView) : LExt st (st.intern w).1 := by
  refine ⟨?_, ?_⟩
  · rw [LStore.ns_intern]; exact NExt.refl _
  · intro i x hd
    simp only [denoteL] at hd ⊢
    have h1 : denoteLAux st ((st.intern w).1.nodeCount + 1) i = some x :=
      denoteLAux_mono st (st.nodeCount + 1) ((st.intern w).1.nodeCount + 1) i x
        (by have := LStore.nodeCount_intern_le st w; omega) hd
    exact denoteLAux_store_mono (fun _ _ hh => LStore.view_intern_mono st w hh)
      (LStore.ns_intern st w) _ i x h1

/-- con-leche: none — arena infrastructure; `LStore.intern_spec` modulo
`LStoreWF`'s missing flag-synchronisation clause (task #97a).  Precedent:
con-leche's retired `Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem LStore.intern_spec_of_sync {st : LStore} {w : LNodeView} (h : LStoreWF st)
    (hsync : st.ScratchSync) (hv : st.ViewOK w) (hcap : st.capOK w) :
    LStoreWF (st.intern w).1 ∧ LExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w :=
  ⟨LStore.intern_wf_of_sync h hsync hv hcap, LStore.intern_ext st w,
   LStore.intern_view_spec h hv hcap⟩


/-! ## `intern` on the level-list store

One constructor, and `LsWF` has no rank clause (a list node has no `LsIdx`
children), so this is the smallest of the four. -/

theorem LsTables.get_inv {t t' : LsTables} {Q : UInt32 → Nat → LsNodeView → Prop}
    {i : LsIdx} {v : LsNodeView}
    (hli : ∀ n a, t'.lists.node? n = some a →
      t.lists.node? n = some a ∨ Q LsTag.list n a.us)
    (h : t'.get i = some v) : t.get i = some v ∨ Q i.tag i.idxNat v := by
  simp only [LsTables.get] at h ⊢
  tag_cases h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hli _) h
  · simp at h

theorem LsTables.get_push_inv {t : LsTables} {w v : LsNodeView} {d : LDer}
    {tr : UInt32} {i : LsIdx} (h : (t.push w d tr).1.get i = some v) :
    t.get i = some v ∨ (i.tag = LsTag.list ∧ i.idxNat = t.sizeOf w ∧ v = w) := by
  refine LsTables.get_inv
    (Q := fun tg n v' => tg = LsTag.list ∧ n = t.sizeOf w ∧ v' = w) ?_ h
  intro n a ha
  simp only [LsTables.push] at ha
  rw [Tbl.node?_push_eq] at ha
  split at ha
  · refine Or.inr ⟨rfl, by simp only [LsTables.sizeOf]; assumption, ?_⟩
    simp only [Option.some.injEq] at ha
    first | (subst ha; rfl) | rfl
  · exact Or.inl ha

theorem LsTables.get_mono {t t' : LsTables}
    (hli : ∀ n a, t.lists.node? n = some a → t'.lists.node? n = some a)
    {i : LsIdx} {v : LsNodeView} (h : t.get i = some v) : t'.get i = some v := by
  simp only [LsTables.get] at h ⊢
  tag_cases h
  · exact Option.map_mono (hli _) h
  · simp at h

theorem LsTables.get_push_mono (t : LsTables) (w : LsNodeView) (d : LDer)
    (tr : UInt32) {i : LsIdx} {v : LsNodeView} (h : t.get i = some v) :
    (t.push w d tr).1.get i = some v := by
  refine LsTables.get_mono ?_ h
  intro n a ha; simp only [LsTables.push]; exact Tbl.node?_push ha

theorem LsTables.push_spec (t : LsTables) (w : LsNodeView) (d : LDer) (tr : UInt32)
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.get (t.push w d tr).2 = some w ∧
      (t.push w d tr).2.tier = tr := by
  simp only [LsTables.sizeOf] at hcap
  have htg : (LsTag.list : UInt32).toNat < 16 := by decide
  have hn := ofNat_lt_cap hcap
  refine ⟨?_, ?_⟩
  · simp only [LsTables.push, LsTables.get, Idx.tag_mk _ _ _ htg htr hn,
      Idx.idxNat_mk _ _ _ htg htr hcap]
    simp [LsTag.list, Tbl.node?_push_new]
  · simp only [LsTables.push, Idx.tier_mk _ _ _ htg htr hn]

theorem LsTables.push_tag {t : LsTables} {w : LsNodeView} {d : LDer} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.tag = LsTag.list := by
  have hn : ((UInt32.ofNat (t.sizeOf w)).toNat) < Idx.idxCap := by
    rw [Idx.idxCap] at hcap ⊢; simp; omega
  simp only [LsTables.push, LsTables.sizeOf] at *
  exact Idx.tag_mk _ _ _ (by decide) htr hn

theorem LsTables.push_idxNat {t : LsTables} {w : LsNodeView} {d : LDer} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).2.idxNat = t.sizeOf w := by
  simp only [LsTables.push, LsTables.sizeOf] at *
  exact Idx.idxNat_mk _ _ _ (by decide) htr hcap

theorem LsTables.find?_push {t : LsTables} {w v : LsNodeView} {d : LDer}
    {tr : UInt32} :
    (t.push w d tr).1.find? v =
      if w = v then some (t.push w d tr).2 else t.find? v := by
  simp only [LsTables.push, LsTables.find?, Tbl.find?_push, beq_iff_eq,
    ListNode.mk.injEq]

theorem LsTables.sizeOf_push {t : LsTables} {w v : LsNodeView} {d : LDer}
    {tr : UInt32} : (t.push w d tr).1.sizeOf v = t.sizeOf w + 1 := by
  simp only [LsTables.push, LsTables.sizeOf, Tbl.size_push]

theorem LsTables.Sized_push {t : LsTables} {w : LsNodeView} {d : LDer} {tr : UInt32}
    (hs : t.Sized) : (t.push w d tr).1.Sized := by
  simp only [LsTables.push, LsTables.Sized]
  exact Tbl.Sized_push hs

theorem LsTables.derAt_congr {t t' : LsTables} {i : LsIdx} {v : LsNodeView}
    (h : t.get i = some v)
    (hli : ∀ n, n < t.lists.size → t'.lists.derAt n = t.lists.derAt n) :
    t'.derAt i = t.derAt i := by
  simp only [LsTables.get] at h
  simp only [LsTables.derAt]
  tag_cases h
  · exact hli _ (Tbl.lt_of_map h)
  · simp at h

theorem LsTables.derAt_push_of_get {t : LsTables} {w : LsNodeView} {d : LDer}
    {tr : UInt32} {i : LsIdx} {v : LsNodeView} (hs : t.Sized)
    (h : t.get i = some v) : (t.push w d tr).1.derAt i = t.derAt i := by
  refine LsTables.derAt_congr h ?_
  intro n hn; simp only [LsTables.push]; exact Tbl.derAt_push_of_lt hs hn

theorem LsTables.derAt_push_new {t : LsTables} {w : LsNodeView} {d : LDer}
    {tr : UInt32} (hs : t.Sized) (htr : tr.toNat < 2)
    (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d tr).1.derAt (t.push w d tr).2 = d := by
  have htag := LsTables.push_tag (t := t) (w := w) (d := d) (tr := tr) htr hcap
  have hix := LsTables.push_idxNat (t := t) (w := w) (d := d) (tr := tr) htr hcap
  simp only [LsTables.sizeOf] at hix
  simp only [LsTables.derAt, htag, hix, beq_self_eq_true, ite_true]
  simp only [LsTables.push]
  exact Tbl.derAt_push_size hs

/-- con-leche: none — the clause `LsStoreWF` is missing (task #97a). -/
def LsStore.ScratchSync (st : LsStore) : Prop := st.scratchOn = st.ls.scratchOn

/-- con-leche: none — the same, off `LsStoreWF`. -/
theorem LsStoreWF.scratchSync {st : LsStore} (h : LsStoreWF st) : st.ScratchSync :=
  LsWF.sync h

theorem LsStore.wf_push_scr {st st' : LsStore} {w : LsNodeView}
    {tb : LsTables} {inew : LsIdx}
    (h : LsWF st) (hv : st.ViewOK w)
    (hon : st.scratchOn = true) (hon' : st'.scratchOn = true)
    (hls : st'.ls = st.ls) (hpers : st'.pers = st.pers)
    (hpush : st.scr.push w (st.derOfView w) Idx.tierS = (tb, inew))
    (hscr : st'.scr = tb)
    (hcap : st.scr.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) (hfs : st.scr.find? w = none) :
    LsStoreWF st' := by
  have htr : (Idx.tierS : UInt32).toNat < 2 := by decide
  have htb : (st.scr.push w (st.derOfView w) Idx.tierS).1 = tb := by rw [hpush]
  have hid : (st.scr.push w (st.derOfView w) Idx.tierS).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (LsTables.push_spec st.scr w _ Idx.tierS htr hcap).1
  have hnp : inew.isPersistent = false := by
    show (inew.tier == 0) = false
    rw [← hid, (LsTables.push_spec st.scr w _ Idx.tierS htr hcap).2]; decide
  have htag : inew.tag = LsTag.list := by rw [← hid]; exact LsTables.push_tag htr hcap
  have hix : inew.idxNat = st.scr.sizeOf w := by
    rw [← hid]; exact LsTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.scr.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact LsTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.scr.get i = some u ∨ (i.tag = LsTag.list ∧ i.idxNat = st.scr.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact LsTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.scr.find? u := by
    intro u; rw [← htb, ← hid]; exact LsTables.find?_push
  have hdertb : ∀ i u, st.scr.get i = some u → tb.derAt i = st.scr.derAt i := by
    intro i u hi; rw [← htb]; exact LsTables.derAt_push_of_get h.sizedS hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact LsTables.derAt_push_new h.sizedS htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact LsTables.Sized_push h.sizedS
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u; rw [← htb, LsTables.sizeOf_push]; omega
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp; rw [LsStore.view_pers hp, LsStore.view_pers hp, hpers]
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = tb.get i := by
    intro i hp; rw [LsStore.view_scr hp hon', hscr]
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp]; exact hu
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp']
      exact hmonotb i u (by rwa [LsStore.view_scr hp' hon] at hu)
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact Or.inl (by rwa [hviewP i hp] at hu)
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [LsStore.view_scr hp' hon]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierS hp').trans (Idx.tier_eq_tierS hnp).symm)
          (h3.trans hix.symm), h4⟩
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp : i.isPersistent = true
    · rw [LsStore.derived_pers hp, LsStore.derived_pers hp, hpers]
    · have hp' : i.isPersistent = false := by simpa using hp
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [LsStore.derived_scr hp' hon', LsStore.derived_scr hp' hon, hscr]
      exact hdertb i u (by rwa [LsStore.view_scr hp' hon] at hu)
  have hdov : ∀ u : LsNodeView, st'.derOfView u = st.derOfView u :=
    fun u => LsStore.derOfView_congr u (fun c _ => by rw [hls])
  refine { ls := by rw [hls]; exact h.ls, lchildOK := ?lchildOK, consP := ?consP,
           consS := ?consS, fresh := ?fresh, derExact := ?derExact,
           sizedP := ?sizedP, sizedS := ?sizedS, capP := ?capP, capS := ?capS,
           scrOff := ?scrOff, sync := by rw [hon', hls, ← h.sync, hon] }
  case lchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hls]; exact h.lchildOK i u hi' c hc
    · refine ⟨by rw [hls]; exact hv c hc, ?_⟩
      intro hpp; exact absurd (hpp.symm.trans hnp) (by simp)
  case consP =>
    intro u i
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
      exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP u i).mpr ⟨by rwa [hviewP i h2] at h1, h2⟩
  case consS =>
    intro u i
    rw [hscr, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consS u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfs] at hf
          exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case fresh =>
    intro u i hf
    rw [hscr, hfindtb u] at hf
    rw [hpers]
    by_cases hw : w = u
    · subst hw; exact hfp
    · rw [ite_eq_right hw] at hf; exact h.fresh u i hf
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u, hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u, LsStore.derived_scr hnp hon', hscr, hdernew]
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact hsizedtb
  case capP => rw [hpers]; exact h.capP
  case capS => rw [hscr]; exact hcaptb
  case scrOff => intro hoff; rw [hon'] at hoff; exact absurd hoff (by simp)

theorem LsStore.wf_push_pers {st st' : LsStore} {w : LsNodeView}
    {tb : LsTables} {inew : LsIdx}
    (h : LsWF st) (hv : st.ViewOK w) (hsync : st.ScratchSync)
    (hon : st.scratchOn = false) (hon' : st'.scratchOn = false)
    (hls : st'.ls = st.ls) (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    LsStoreWF st' := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have hscrE : st.scr = LsTables.empty := h.scrOff hon
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (LsTables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (LsTables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = LsTag.list := by rw [← hid]; exact LsTables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact LsTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact LsTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨ (i.tag = LsTag.list ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact LsTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact LsTables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact LsTables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact LsTables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact LsTables.Sized_push h.sizedP
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u; rw [← htb, LsTables.sizeOf_push]; omega
  have hlsoff : st.ls.scratchOn = false := by rw [← hsync]; exact hon
  have hallPL : ∀ c : LIdx, (st.ls.view c).isSome = true → c.isPersistent = true := by
    intro c hc
    by_cases hp : c.isPersistent = true
    · exact hp
    · rw [LStore.view_off (by simpa using hp) hlsoff] at hc; exact absurd hc (by simp)
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp; rw [LsStore.view_pers hp, hpers]
  have hviewN' : ∀ i, i.isPersistent = false → st'.view i = none :=
    fun i hp => LsStore.view_off hp hon'
  have hviewN : ∀ i, i.isPersistent = false → st.view i = none :=
    fun i hp => LsStore.view_off hp hon
  have hallP : ∀ i u, st.view i = some u → i.isPersistent = true := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · exact hp
    · rw [hviewN i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    have hp := hallP i u hu
    rw [hviewP i hp]
    exact hmonotb i u (by rwa [LsStore.view_pers hp] at hu)
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [LsStore.view_pers hp]; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp).trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewN' i (by simpa using hp)] at hu; exact absurd hu (by simp)
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    have hp := hallP i u hu
    rw [LsStore.derived_pers hp, LsStore.derived_pers hp, hpers]
    exact hdertb i u (by rwa [LsStore.view_pers hp] at hu)
  have hdov : ∀ u : LsNodeView, st'.derOfView u = st.derOfView u :=
    fun u => LsStore.derOfView_congr u (fun c _ => by rw [hls])
  refine { ls := by rw [hls]; exact h.ls, lchildOK := ?lchildOK, consP := ?consP,
           consS := ?consS, fresh := ?fresh, derExact := ?derExact,
           sizedP := ?sizedP, sizedS := ?sizedS, capP := ?capP, capS := ?capS,
           scrOff := ?scrOff, sync := by rw [hon', hls, ← h.sync, hon] }
  case lchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hls]; exact h.lchildOK i u hi' c hc
    · exact ⟨by rw [hls]; exact hv c hc, fun _ => hallPL c (hv c hc)⟩
  case consP =>
    intro u i
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consS =>
    intro u i
    rw [hscr, hscrE, LsTables.find?_empty]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hviewN' i h2] at h1; exact absurd h1 (by simp)
  case fresh =>
    intro u i hf
    rw [hscr, hscrE, LsTables.find?_empty] at hf
    exact absurd hf (by simp)
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u, hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u, LsStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro _; rw [hscr]; exact hscrE

theorem LsStore.intern_wf_of_sync {st : LsStore} {w : LsNodeView} (h : LsStoreWF st)
    (hsync : st.ScratchSync) (hv : st.ViewOK w) (hcap : st.capOK w) :
    LsStoreWF (st.intern w).1 := by
  simp only [LsStore.capOK] at hcap
  simp only [LsStore.intern]
  split
  · exact h
  · rename_i hfp
    split
    · rename_i hon
      split
      · exact h
      · rename_i hfs
        rw [ite_eq_left hon] at hcap
        exact LsStore.wf_push_scr h hv hon hon rfl rfl rfl rfl hcap hfp hfs
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [ite_eq_right hoff] at hcap
      exact LsStore.wf_push_pers h hv hsync hoff' hoff' rfl rfl rfl rfl hcap hfp

theorem LsStore.intern_view_spec {st : LsStore} {w : LsNodeView} (h : LsStoreWF st)
    (_hv : st.ViewOK w) (hcap : st.capOK w) :
    (st.intern w).1.view (st.intern w).2 = some w := by
  simp only [LsStore.capOK] at hcap
  simp only [LsStore.intern]
  split
  · rename_i i heq
    exact ((h.consP w i).mp heq).1
  · split
    · rename_i hon
      split
      · rename_i i heq
        exact ((h.consS w i).mp heq).1
      · rw [ite_eq_left hon] at hcap
        have hspec := LsTables.push_spec st.scr w (st.derOfView w) Idx.tierS
          (by decide) hcap
        have hp : ((st.scr.push w (st.derOfView w) Idx.tierS).2).isPersistent = false := by
          show (_ == 0) = false
          rw [hspec.2]; decide
        simp only [LsStore.view]
        rw [ite_eq_right (by simp [hp]), ite_eq_left hon]
        exact hspec.1
    · rename_i hoff
      rw [ite_eq_right hoff] at hcap
      have hspec := LsTables.push_spec st.pers w (st.derOfView w) Idx.tierP
        (by decide) hcap
      have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [LsStore.view]
      rw [ite_eq_left hp]
      exact hspec.1

theorem LsStore.ls_intern (st : LsStore) (w : LsNodeView) :
    (st.intern w).1.ls = st.ls := by
  simp only [LsStore.intern]
  split
  · rfl
  · split
    · split
      · rfl
      · rfl
    · rfl

theorem LsStore.view_intern_mono (st : LsStore) (w : LsNodeView) {i : LsIdx}
    {v : LsNodeView} (h : st.view i = some v) : (st.intern w).1.view i = some v := by
  simp only [LsStore.intern]
  split
  · exact h
  · split
    · rename_i hon
      split
      · exact h
      · simp only [LsStore.view, hon] at h ⊢
        by_cases hp : i.isPersistent = true
        · rw [ite_eq_left hp] at h ⊢; exact h
        · rw [ite_eq_right hp] at h ⊢; exact LsTables.get_push_mono _ _ _ _ h
    · rename_i hoff
      simp only [LsStore.view, hoff] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [ite_eq_left hp] at h ⊢; exact LsTables.get_push_mono _ _ _ _ h
      · rw [ite_eq_right hp] at h ⊢; exact h

/-- con-leche: none — arena infrastructure; interning a level list extends
the store.  `denoteLs` carries no fuel, so this is `view` monotonicity and
the level store standing still.  Precedent: con-leche's retired
`Verify/SimI.lean:244 Ext` (at 94a1cf78). -/
theorem LsStore.intern_ext (st : LsStore) (w : LsNodeView) :
    LsExt st (st.intern w).1 := by
  refine ⟨?_, ?_⟩
  · rw [LsStore.ls_intern]; exact LExt.refl _
  · intro i us hd
    obtain ⟨vs, hvs, hlist⟩ := denoteLs_view hd
    rw [denoteLs, LsStore.view_intern_mono st w hvs, LsStore.ls_intern]
    exact hlist

/-- con-leche: none — arena infrastructure; `LsStore.intern_spec` modulo
`LsStoreWF`'s missing flag-synchronisation clause (task #97a).  Precedent:
con-leche's retired `Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem LsStore.intern_spec_of_sync {st : LsStore} {w : LsNodeView}
    (h : LsStoreWF st) (hsync : st.ScratchSync) (hv : st.ViewOK w)
    (hcap : st.capOK w) :
    LsStoreWF (st.intern w).1 ∧ LsExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w :=
  ⟨LsStore.intern_wf_of_sync h hsync hv hcap, LsStore.intern_ext st w,
   LsStore.intern_view_spec h hv hcap⟩

/-- con-leche: none — arena infrastructure; `intern` preserves the store
invariant.  The flag synchronisation the persistent case needs is
`EWFAt.sync`, read off `StoreWF` (task #97a).  Precedent: con-leche's
retired `Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem EStore.intern_wf {st : EStore} {w : ENodeView} (h : StoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) : StoreWF (st.intern w).1 :=
  EStore.intern_wf_of_sync h h.scratchSync hv hcap

/-- con-leche: none — arena infrastructure; **`intern_spec`**: the store
stays well formed, the arena only grows, the new handle decodes to the node
that was interned, and it denotes that node's denotation.  Precedent:
con-leche's retired `Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
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

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/IExpr.lean:472 enableTierTwo` (at 94a1cf78). -/
theorem EStore.enableScratch_wf {st : EStore} (h : StoreWF st) :
    StoreWF st.enableScratch := by
  obtain ⟨rk, h⟩ := h
  exact ⟨rk, EStore.enableScratch_wfAt h⟩

/-- con-leche: none — arena infrastructure; opening the scratch tier keeps
the invariant and changes no persistent handle.  Precedent: con-leche's
retired `Setlec/Kernel/IExpr.lean:472 enableTierTwo` (at 94a1cf78). -/
theorem EStore.enableScratch_spec {st : EStore} (h : StoreWF st) :
    StoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) ∧
      (∀ i, i.isPersistent = false → denoteE st.enableScratch i = none) :=
  ⟨EStore.enableScratch_wf h, fun _ hp => EStore.view_enableScratch_pers_wf h hp,
   fun _ hp => denoteE_enableScratch_scr st hp⟩

/-- con-leche: none — arena infrastructure.  Precedent: con-leche's retired
`Setlec/Kernel/IExpr.lean:480 truncateTierTwo` (at 94a1cf78). -/
theorem EStore.dropScratch_wf {st : EStore} (h : StoreWF st) :
    StoreWF st.dropScratch := by
  obtain ⟨rk, h⟩ := h
  exact ⟨rk, EStore.dropScratch_wfAt h⟩

/-- con-leche: none — arena infrastructure; dropping the scratch tier keeps
every persistent denotation and invalidates every scratch handle.
Precedent: con-leche's retired `Setlec/Kernel/IExpr.lean:480
truncateTierTwo` (at 94a1cf78). -/
theorem EStore.dropScratch_denote_pers {st : EStore} (h : StoreWF st)
    {i : EIdx} {e : Expr} (hp : i.isPersistent = true)
    (hd : denoteE st i = some e) : denoteE st.dropScratch i = some e := by
  obtain ⟨rk, h⟩ := h
  have h' := EStore.dropScratch_wfAt h
  obtain ⟨v, hv⟩ := denoteE_view hd
  have hsome : (st.dropScratch.view i).isSome = true := by
    rw [EStore.view_dropScratch_pers st hp, hv]; rfl
  have hr1 : rk i < st.dropScratch.nodeCount := h'.rank_lt hsome
  have hr2 : rk i < st.nodeCount := h.rank_lt (by rw [hv]; rfl)
  have h1 : denoteEAux st.dropScratch (st.nodeCount + 1) i = some e :=
    denoteEAux_dropScratch h _ i e hp hd
  rw [denoteE, denoteEAux_congr h' (st.dropScratch.nodeCount + 1) i
    (st.dropScratch.nodeCount + 1) (st.nodeCount + 1) (by omega) (by omega) (by omega)]
  exact h1

/-- con-leche: none — arena infrastructure; **the** tier discipline in one
statement.  Precedent: con-leche's retired `Setlec/Kernel/IExpr.lean:480
truncateTierTwo` (at 94a1cf78). -/
theorem EStore.dropScratch_spec {st : EStore} (h : StoreWF st) :
    StoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i e, i.isPersistent = true → denoteE st i = some e →
        denoteE st.dropScratch i = some e) ∧
      (∀ i, i.isPersistent = false → denoteE st.dropScratch i = none) :=
  ⟨EStore.dropScratch_wf h, fun _ hp => EStore.view_dropScratch_pers_wf h hp,
   fun _ _ hp hd => EStore.dropScratch_denote_pers h hp hd,
   fun _ hp => denoteE_dropScratch_scr st hp⟩

/-! ### The same, for the three stores underneath

Names, levels and level lists have the identical shape; their `Ext`,
`intern_spec`, `enableScratch_spec` and `dropScratch_spec` are the same
arguments over three / five / one constructor arrays instead of ten. -/

theorem NStore.intern_spec {st : NStore} {w : NNodeView} (h : NStoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    NStoreWF (st.intern w).1 ∧ NExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w :=
  ⟨NStore.intern_wf h hv hcap, NStore.intern_ext st w,
   NStore.intern_view_spec h hv hcap⟩

/-- `LWFAt.nchildOK` asks a persistent level node's *name* child to be
persistent; `LWFAt.sync` ties `st.ns.scratchOn` to `st.scratchOn`, which is
what makes that provable (task #97a). -/
theorem LStore.intern_spec {st : LStore} {w : LNodeView} (h : LStoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    LStoreWF (st.intern w).1 ∧ LExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w :=
  LStore.intern_spec_of_sync h h.scratchSync hv hcap

/-- `LsWF.lchildOK` asks a persistent list node's *level* children to be
persistent; `LsWF.sync` ties `st.ls.scratchOn` to `st.scratchOn`, which is
what makes that provable (task #97a). -/
theorem LsStore.intern_spec {st : LsStore} {w : LsNodeView} (h : LsStoreWF st)
    (hv : st.ViewOK w) (hcap : st.capOK w) :
    LsStoreWF (st.intern w).1 ∧ LsExt st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w :=
  LsStore.intern_spec_of_sync h h.scratchSync hv hcap

theorem NStore.dropScratch_spec {st : NStore} (h : NStoreWF st) :
    NStoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i x, i.isPersistent = true → denoteN st i = some x →
        denoteN st.dropScratch i = some x) := by
  obtain ⟨rk, h⟩ := h
  exact ⟨⟨rk, NStore.dropScratch_wfAt h⟩,
    fun _ hp => NStore.view_dropScratch_pers st hp,
    fun _ _ hp hd => denoteN_dropScratch_pers h hp hd⟩

theorem LStore.dropScratch_spec {st : LStore} (h : LStoreWF st) :
    LStoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i x, i.isPersistent = true → denoteL st i = some x →
        denoteL st.dropScratch i = some x) := by
  obtain ⟨rk, h⟩ := h
  exact ⟨⟨rk, LStore.dropScratch_wfAt h⟩,
    fun _ hp => LStore.view_dropScratch_pers st hp,
    fun _ _ hp hd => denoteL_dropScratch_pers h hp hd⟩

theorem LsStore.dropScratch_spec {st : LsStore} (h : LsStoreWF st) :
    LsStoreWF st.dropScratch ∧
      (∀ i, i.isPersistent = true → st.dropScratch.view i = st.view i) ∧
      (∀ i x, i.isPersistent = true → denoteLs st i = some x →
        denoteLs st.dropScratch i = some x) := by
  exact ⟨LsStore.dropScratch_wf h,
    fun _ hp => LsStore.view_dropScratch_pers st hp,
    fun _ _ hp hd => denoteLs_dropScratch_pers h hp hd⟩

/-! ## The cons HIT answers a handle whose view is the view (task #97-P5-1's
finding 9)

**The twin/Rust divergence this closes.**  The Rust tests `Tbl::full` only
where it is about to APPEND — inside the cons-table miss path — so on a cons
HIT at a full constructor array it answers `Ok`, while a twin that tested the
capacity BEFORE probing threw `native`.  `Arena/Monad.lean`'s `internE`,
`internPersistentE` and the three nested wrappers now probe first and test the
capacity on the miss path only, which is the Rust's own order.

What the hit path owes the bridge is one fact per store, and it is `StoreWF`'s
own `consP` / `consS` clause read left to right: a handle the cons table
answers for a view is a handle whose view is that view.  No capacity anywhere
in it — which is the point. -/

/-- con-leche: none — arena infrastructure; the two-tier probe answers only
what one of the two tiers answered. -/
theorem NStore.find?_cases {st : NStore} {v : NNodeView} {i : NIdx}
    (hf : st.find? v = some i) :
    st.pers.find? v = some i ∨ st.scr.find? v = some i := by
  simp only [NStore.find?] at hf
  split at hf
  · rename_i j hp
    obtain rfl := Option.some.inj hf
    exact Or.inl hp
  · split at hf
    · exact Or.inr hf
    · exact absurd hf (by simp)

/-- con-leche: none — arena infrastructure; a name-store cons hit names a node
with that view. -/
theorem NStore.view_of_find {st : NStore} {v : NNodeView} {i : NIdx}
    (h : NStoreWF st) (hf : st.find? v = some i) : st.view i = some v := by
  obtain ⟨rk, hwf⟩ := h
  rcases NStore.find?_cases hf with hh | hh
  · exact ((hwf.consP v i).mp hh).1
  · exact ((hwf.consS v i).mp hh).1

/-- con-leche: none — arena infrastructure; the same at the level store. -/
theorem LStore.find?_cases {st : LStore} {v : LNodeView} {i : LIdx}
    (hf : st.find? v = some i) :
    st.pers.find? v = some i ∨ st.scr.find? v = some i := by
  simp only [LStore.find?] at hf
  split at hf
  · rename_i j hp
    obtain rfl := Option.some.inj hf
    exact Or.inl hp
  · split at hf
    · exact Or.inr hf
    · exact absurd hf (by simp)

/-- con-leche: none — arena infrastructure; a level-store cons hit. -/
theorem LStore.view_of_find {st : LStore} {v : LNodeView} {i : LIdx}
    (h : LStoreWF st) (hf : st.find? v = some i) : st.view i = some v := by
  obtain ⟨rk, hwf⟩ := h
  rcases LStore.find?_cases hf with hh | hh
  · exact ((hwf.consP v i).mp hh).1
  · exact ((hwf.consS v i).mp hh).1

/-- con-leche: none — arena infrastructure; the same at the level-list
store. -/
theorem LsStore.find?_cases {st : LsStore} {v : LsNodeView} {i : LsIdx}
    (hf : st.find? v = some i) :
    st.pers.find? v = some i ∨ st.scr.find? v = some i := by
  simp only [LsStore.find?] at hf
  split at hf
  · rename_i j hp
    obtain rfl := Option.some.inj hf
    exact Or.inl hp
  · split at hf
    · exact Or.inr hf
    · exact absurd hf (by simp)

/-- con-leche: none — arena infrastructure; a level-list cons hit. -/
theorem LsStore.view_of_find {st : LsStore} {v : LsNodeView} {i : LsIdx}
    (h : LsStoreWF st) (hf : st.find? v = some i) : st.view i = some v := by
  rcases LsStore.find?_cases hf with hh | hh
  · exact ((h.consP v i).mp hh).1
  · exact ((h.consS v i).mp hh).1

/-- con-leche: none — arena infrastructure; the expression store's two-tier
probe. -/
theorem EStore.find?_cases {st : EStore} {v : ENodeView} {i : EIdx}
    (hf : st.find? v = some i) :
    st.persFind? v = some i ∨ st.scrFind? v = some i := by
  simp only [EStore.find?] at hf
  simp only [EStore.persFind?, EStore.scrFind?]
  split at hf
  · rename_i j hp
    obtain rfl := Option.some.inj hf
    exact Or.inl (EStore.pers_find_of_persFindMaybe hp)
  · split at hf
    · exact Or.inr hf
    · exact absurd hf (by simp)

/-- con-leche: none — arena infrastructure; an expression-store cons hit names
a node with that view. -/
theorem EStore.view_of_find {st : EStore} {v : ENodeView} {i : EIdx}
    (h : StoreWF st) (hf : st.find? v = some i) : st.view i = some v := by
  obtain ⟨rk, hwf⟩ := h
  rcases EStore.find?_cases hf with hh | hh
  · exact ((hwf.consP v i).mp hh).1
  · exact ((hwf.consS v i).mp hh).1

/-! ### The extension combinators

`intern_ext` above proves `Ext st (st.intern w).1` by hand — `view`
monotonicity, then the fuel traded up through `denoteEAux_mono`, then
`denoteEAux_store_mono`.  Every other appending primitive owes the same three
steps, so they are taken ONCE here, as `{N,L,Ls,}Ext.of_view_mono`: give the
combinator the tier's own `view` monotonicity, the nested store's extension
and the node count's monotonicity, and it hands back the extension.  With them
each of the `…_ext` theorems below is three lines and no induction.

Two of the four need a generalisation of the `denote…Aux_store_mono` above
them: those are stated with the nested store held FIXED (`st'.ns = st.ns`,
`st'.lss = st.lss`), which is true of `intern` at the expression tier and
false of `internName`/`internLevel`/`internLevels`, whose whole business is to
move it.  `denoteLAux_store_mono_ns` and `denoteEAux_store_mono_lss` take the
nested EXTENSION instead, which is the weakest hypothesis the `param` /
`sort` / `const` / `proj` arms actually use. -/

/-- con-leche: none — arena infrastructure; a name store that decodes every
handle the old one decoded, and holds at least as many nodes, extends it. -/
theorem NExt.of_view_mono {st st' : NStore}
    (hv : ∀ i v, st.view i = some v → st'.view i = some v)
    (hc : st.nodeCount ≤ st'.nodeCount) : NExt st st' := by
  intro i x hd
  simp only [denoteN] at hd ⊢
  have h1 : denoteNAux st (st'.nodeCount + 1) i = some x :=
    denoteNAux_mono st (st.nodeCount + 1) (st'.nodeCount + 1) i x (by omega) hd
  exact denoteNAux_store_mono hv _ i x h1

theorem denoteLAux_store_mono_ns {st st' : LStore}
    (hv : ∀ i v, st.view i = some v → st'.view i = some v)
    (hns : NExt st.ns st'.ns) :
    ∀ (f : Nat) (i : LIdx) (x : Level),
      denoteLAux st f i = some x → denoteLAux st' f i = some x := by
  intro f
  induction f with
  | zero => intro i x hd; simp [denoteLAux] at hd
  | succ k ih =>
    intro i x hd
    simp only [denoteLAux, Option.bind_eq_some_iff] at hd ⊢
    obtain ⟨v, hvv, hd⟩ := hd
    refine ⟨v, hv i v hvv, ?_⟩
    cases v with
    | zero => exact hd
    | param n =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, hns n q hq, he⟩
    | succ u =>
      simp only [Option.map_eq_some_iff] at hd ⊢
      obtain ⟨q, hq, he⟩ := hd
      exact ⟨q, ih u q hq, he⟩
    | max u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ha, ih w b hb, he⟩
    | imax u w =>
      simp only [opt2_eq_some_iff] at hd ⊢
      obtain ⟨a, b, ha, hb, he⟩ := hd
      exact ⟨a, b, ih u a ha, ih w b hb, he⟩

/-- con-leche: none — arena infrastructure; the same at the level tier, with
the name store's own extension carried in. -/
theorem LExt.of_view_mono {st st' : LStore} (hns : NExt st.ns st'.ns)
    (hv : ∀ i v, st.view i = some v → st'.view i = some v)
    (hc : st.nodeCount ≤ st'.nodeCount) : LExt st st' := by
  refine ⟨hns, ?_⟩
  intro i x hd
  simp only [denoteL] at hd ⊢
  have h1 : denoteLAux st (st'.nodeCount + 1) i = some x :=
    denoteLAux_mono st (st.nodeCount + 1) (st'.nodeCount + 1) i x (by omega) hd
  exact denoteLAux_store_mono_ns hv hns _ i x h1

theorem denoteLList_mono_of_lext {st st' : LStore} (hls : LExt st st') :
    ∀ (vs : List LIdx) (us : List Level),
      denoteLList st vs = some us → denoteLList st' vs = some us := by
  intro vs
  induction vs with
  | nil => intro us hd; exact hd
  | cons a as ih =>
    intro us hd
    simp only [denoteLList, opt2_eq_some_iff] at hd ⊢
    obtain ⟨x, y, hx, hy, he⟩ := hd
    exact ⟨x, y, hls.lvl a x hx, ih y hy, he⟩

/-- con-leche: none — arena infrastructure; the same at the level-list tier.
There is no fuel here, so there is no count hypothesis. -/
theorem LsExt.of_view_mono {st st' : LsStore} (hls : LExt st.ls st'.ls)
    (hv : ∀ i v, st.view i = some v → st'.view i = some v) : LsExt st st' := by
  refine ⟨hls, ?_⟩
  intro i us hd
  obtain ⟨vs, hvs, hlist⟩ := denoteLs_view hd
  rw [denoteLs, hv i vs hvs]
  exact denoteLList_mono_of_lext hls vs us hlist

theorem denoteEAux_store_mono_lss {st st' : EStore}
    (hv : ∀ i v, st.view i = some v → st'.view i = some v)
    (hlss : LsExt st.lss st'.lss) :
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
    cases v with
    | bvar _ => exact h
    | lit _ => exact h
    | sort u =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨q, hq, he⟩ := h
      exact ⟨q, hlss.ls.lvl u q hq, he⟩
    | const n l =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, hlss.ls.ns n x hx, hlss.lst l y hy, he⟩
    | fvar j ty =>
      simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨q, hq, he⟩ := h
      exact ⟨q, ih ty q hq, he⟩
    | proj n j e' =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, hlss.ls.ns n x hx, ih e' y hy, he⟩
    | app a b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih a x hx, ih b y hy, he⟩
    | lam ty b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih ty x hx, ih b y hy, he⟩
    | forallE ty b =>
      simp only [opt2_eq_some_iff] at h ⊢
      obtain ⟨x, y, hx, hy, he⟩ := h
      exact ⟨x, y, ih ty x hx, ih b y hy, he⟩
    | letE ty w b =>
      simp only [opt3_eq_some_iff] at h ⊢
      obtain ⟨x, y, z, hx, hy, hz, he⟩ := h
      exact ⟨x, y, z, ih ty x hx, ih w y hy, ih b z hz, he⟩

/-- con-leche: none — arena infrastructure; **the combinator every `…_ext`
below is an instance of**: `view` monotonicity, plus the nested store's
extension, plus a node count that did not shrink, IS `Ext`. -/
theorem Ext.of_view_mono {st st' : EStore} (hlss : LsExt st.lss st'.lss)
    (hv : ∀ i v, st.view i = some v → st'.view i = some v)
    (hc : st.nodeCount ≤ st'.nodeCount) : Ext st st' := by
  refine ⟨hlss, ?_⟩
  intro i e hd
  simp only [denoteE] at hd ⊢
  have h1 : denoteEAux st (st'.nodeCount + 1) i = some e :=
    denoteEAux_mono st (st.nodeCount + 1) (st'.nodeCount + 1) i e (by omega) hd
  exact denoteEAux_store_mono_lss hv hlss _ i e h1

/-! ### `pushBind`, the binder append's own plumbing

`ETables.pushBind` appends a binder RECORD to the array its tag names.  It
touches `lams` or `foralls` and nothing else, so it is `push` at the binder
view the tag spells. -/

theorem ETables.get_pushBind_mono (t : ETables) (tag : UInt32) (r : BindNode)
    (d : UInt64) (tier : UInt32) {i : EIdx} {v : ENodeView}
    (h : t.get i = some v) : (t.pushBind tag r d tier).1.get i = some v := by
  refine ETables.get_mono ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;> intro n a ha <;>
    (simp only [ETables.pushBind]; split) <;>
    first | exact ha | exact Tbl.node?_push ha

theorem ETables.getBind_pushBind_mono (t : ETables) (tag : UInt32) (r : BindNode)
    (d : UInt64) (tier : UInt32) {i : EIdx} {p : EIdx × EIdx}
    (h : t.getBind i = some p) : (t.pushBind tag r d tier).1.getBind i = some p := by
  refine ETables.getBind_mono ?_ ?_ h <;> intro n a ha <;>
    (simp only [ETables.pushBind]; split) <;>
    first | exact ha | exact Tbl.node?_push ha

/-! ### `internBind` — `intern` at a binder record

`internBind tag ty b` is `intern` at the binder view `tag` spells, whenever
`tag` is one of the two binder tags (`internBind_eq_intern`); the lemmas below
are also taken directly on `pushBind`, unconditionally — an append moves no
handle that decoded before it, whatever the store's invariant says. -/

theorem EStore.internBind_eq_intern (st : EStore) (tag : UInt32) (ty b : EIdx)
    (ht : tag = ETag.lam ∨ tag = ETag.forallE) :
    st.internBind tag ty b = st.intern (eBindView tag ty b) := by
  rcases ht with rfl | rfl <;> rfl

theorem EStore.findBind_eq_find (st : EStore) (tag : UInt32) (ty b : EIdx)
    (ht : tag = ETag.lam ∨ tag = ETag.forallE) :
    st.findBind tag ty b = st.find? (eBindView tag ty b) := by
  rcases ht with rfl | rfl <;> rfl

/-- `internBind`'s three outcomes: a cons hit moves nothing, a miss appends
the binder record to the tier the store is in. -/
theorem EStore.internBind_cases (st : EStore) (tag : UInt32) (ty b : EIdx) :
    (st.internBind tag ty b).1 = st ∨
      (st.internBind tag ty b).1 =
        { st with scr := (st.scr.pushBind tag ⟨ty, b⟩
            (st.derOfBindAt (if tag == ETag.lam then 19 else 23) ty b)
            Idx.tierS).1 } ∨
      (st.internBind tag ty b).1 =
        { st with pers := (st.pers.pushBind tag ⟨ty, b⟩
            (st.derOfBindAt (if tag == ETag.lam then 19 else 23) ty b)
            Idx.tierP).1 } := by
  simp only [EStore.internBind]
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem EStore.view_internBind_mono (st : EStore) (tag : UInt32) (ty b : EIdx)
    {i : EIdx} {v : ENodeView} (h : st.view i = some v) :
    (st.internBind tag ty b).1.view i = some v := by
  rcases EStore.internBind_cases st tag ty b with he | he | he <;> rw [he]
  · exact h
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => ETables.get_pushBind_mono _ _ _ _ _ hh
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => ETables.get_pushBind_mono _ _ _ _ _ hh
    · exact fun _ _ hh => hh

theorem EStore.scratchOn_internBind (st : EStore) (tag : UInt32) (ty b : EIdx) :
    (st.internBind tag ty b).1.scratchOn = st.scratchOn := by
  rcases EStore.internBind_cases st tag ty b with he | he | he <;> rw [he]

/-! ### The persistent-tier append

`EStore.internPersistent` (task #97-P6-2): `intern`'s `else` branch with the
scratch probe left out, so the append lands in `pers` whatever tier the store
is in.  `Ext` does not care which tier grew — it is `view` monotonicity and a
node count — so these are the same lines as their `intern` siblings.  (The
INVARIANT does care: `fresh` is transiently broken by a promotion.) -/

theorem EStore.internPersistent_cases (st : EStore) (v : ENodeView) :
    (st.internPersistent v).1 = st ∨
      (st.internPersistent v).1 =
        { st with pers := (st.pers.push v (st.derOfView v) Idx.tierP).1 } := by
  simp only [EStore.internPersistent]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem EStore.view_internPersistent_mono (st : EStore) (w : ENodeView)
    {i : EIdx} {v : ENodeView} (h : st.view i = some v) :
    (st.internPersistent w).1.view i = some v := by
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he]
  · exact h
  · refine EStore.view_mono_of_tiers _ _ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => ETables.get_push_mono _ _ _ _ hh
    · exact fun _ _ hh => hh

theorem EStore.lss_internPersistent (st : EStore) (w : ENodeView) :
    (st.internPersistent w).1.lss = st.lss := by
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he]

theorem EStore.scratchOn_internPersistent (st : EStore) (w : ENodeView) :
    (st.internPersistent w).1.scratchOn = st.scratchOn := by
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he]

theorem EStore.nodeCount_internPersistent_le (st : EStore) (w : ENodeView) :
    st.nodeCount ≤ (st.internPersistent w).1.nodeCount := by
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he]
  · omega
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_push]
    omega

/-! ### The three nested stores' persistent append -/

theorem NStore.internPersistent_cases (st : NStore) (w : NNodeView) :
    (st.internPersistent w).1 = st ∨
      (st.internPersistent w).1 =
        { st with pers := (st.pers.push w (st.derOfView w) Idx.tierP).1 } := by
  simp only [NStore.internPersistent]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem NStore.view_internPersistent_mono (st : NStore) (w : NNodeView) {i : NIdx}
    {v : NNodeView} (h : st.view i = some v) :
    (st.internPersistent w).1.view i = some v := by
  rcases NStore.internPersistent_cases st w with he | he <;> rw [he]
  · exact h
  · simp only [NStore.view] at h ⊢
    by_cases hp : i.isPersistent = true
    · rw [ite_eq_left hp] at h ⊢; exact NTables.get_push_mono _ _ _ _ h
    · rw [ite_eq_right hp] at h ⊢; exact h

theorem NStore.scratchOn_internPersistent (st : NStore) (w : NNodeView) :
    (st.internPersistent w).1.scratchOn = st.scratchOn := by
  rcases NStore.internPersistent_cases st w with he | he <;> rw [he]

theorem NStore.nodeCount_internPersistent_le (st : NStore) (w : NNodeView) :
    st.nodeCount ≤ (st.internPersistent w).1.nodeCount := by
  rcases NStore.internPersistent_cases st w with he | he <;> rw [he]
  · exact Nat.le_refl _
  · simp only [NStore.nodeCount, NStore.persCount, NStore.scrCount,
      NTables.count_push]
    omega

theorem LStore.internPersistent_cases (st : LStore) (w : LNodeView) :
    (st.internPersistent w).1 = st ∨
      (st.internPersistent w).1 =
        { st with pers := (st.pers.push w (st.derOfView w) Idx.tierP).1 } := by
  simp only [LStore.internPersistent]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem LStore.ns_internPersistent (st : LStore) (w : LNodeView) :
    (st.internPersistent w).1.ns = st.ns := by
  rcases LStore.internPersistent_cases st w with he | he <;> rw [he]

theorem LStore.view_internPersistent_mono (st : LStore) (w : LNodeView) {i : LIdx}
    {v : LNodeView} (h : st.view i = some v) :
    (st.internPersistent w).1.view i = some v := by
  rcases LStore.internPersistent_cases st w with he | he <;> rw [he]
  · exact h
  · simp only [LStore.view] at h ⊢
    by_cases hp : i.isPersistent = true
    · rw [ite_eq_left hp] at h ⊢; exact LTables.get_push_mono _ _ _ _ h
    · rw [ite_eq_right hp] at h ⊢; exact h

theorem LStore.scratchOn_internPersistent (st : LStore) (w : LNodeView) :
    (st.internPersistent w).1.scratchOn = st.scratchOn := by
  rcases LStore.internPersistent_cases st w with he | he <;> rw [he]

theorem LStore.nodeCount_internPersistent_le (st : LStore) (w : LNodeView) :
    st.nodeCount ≤ (st.internPersistent w).1.nodeCount := by
  rcases LStore.internPersistent_cases st w with he | he <;> rw [he]
  · exact Nat.le_refl _
  · simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount,
      LTables.count_push]
    omega

theorem LsStore.internPersistent_cases (st : LsStore) (w : LsNodeView) :
    (st.internPersistent w).1 = st ∨
      (st.internPersistent w).1 =
        { st with pers := (st.pers.push w (st.derOfView w) Idx.tierP).1 } := by
  simp only [LsStore.internPersistent]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem LsStore.ls_internPersistent (st : LsStore) (w : LsNodeView) :
    (st.internPersistent w).1.ls = st.ls := by
  rcases LsStore.internPersistent_cases st w with he | he <;> rw [he]

theorem LsStore.view_internPersistent_mono (st : LsStore) (w : LsNodeView)
    {i : LsIdx} {v : LsNodeView} (h : st.view i = some v) :
    (st.internPersistent w).1.view i = some v := by
  rcases LsStore.internPersistent_cases st w with he | he <;> rw [he]
  · exact h
  · simp only [LsStore.view] at h ⊢
    by_cases hp : i.isPersistent = true
    · rw [ite_eq_left hp] at h ⊢; exact LsTables.get_push_mono _ _ _ _ h
    · rw [ite_eq_right hp] at h ⊢; exact h

theorem LsStore.scratchOn_internPersistent (st : LsStore) (w : LsNodeView) :
    (st.internPersistent w).1.scratchOn = st.scratchOn := by
  rcases LsStore.internPersistent_cases st w with he | he <;> rw [he]

/-! ### The `Ext` theorems, one per appending entry point

Each is `…Ext.of_view_mono` at the three plumbing lemmas above it.  Together
with `EStore.intern_ext` they cover every primitive of `Store.lean` that
appends: the four node stores' `intern` and `internPersistent`, the binder
entry `internBind`, and the six lifts through the nesting. -/

theorem NStore.internPersistent_ext (st : NStore) (w : NNodeView) :
    NExt st (st.internPersistent w).1 :=
  NExt.of_view_mono (fun _ _ h => NStore.view_internPersistent_mono st w h)
    (NStore.nodeCount_internPersistent_le st w)

theorem LStore.internPersistent_ext (st : LStore) (w : LNodeView) :
    LExt st (st.internPersistent w).1 :=
  LExt.of_view_mono (by rw [LStore.ns_internPersistent]; exact NExt.refl _)
    (fun _ _ h => LStore.view_internPersistent_mono st w h)
    (LStore.nodeCount_internPersistent_le st w)

theorem LsStore.internPersistent_ext (st : LsStore) (w : LsNodeView) :
    LsExt st (st.internPersistent w).1 :=
  LsExt.of_view_mono (by rw [LsStore.ls_internPersistent]; exact LExt.refl _)
    (fun _ _ h => LsStore.view_internPersistent_mono st w h)

theorem EStore.nodeCount_internBind_le (st : EStore) (tag : UInt32) (ty b : EIdx) :
    st.nodeCount ≤ (st.internBind tag ty b).1.nodeCount := by
  rcases EStore.internBind_cases st tag ty b with he | he | he <;> rw [he]
  · exact Nat.le_refl _
  all_goals
    simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.count,
      ETables.pushBind]
    split <;> simp only [Tbl.size_push] <;> omega

/-- con-leche: none — arena infrastructure; the binder entry extends the
arena. -/
theorem EStore.internBind_ext (st : EStore) (tag : UInt32) (ty b : EIdx) :
    Ext st (st.internBind tag ty b).1 :=
  Ext.of_view_mono (by
      rcases EStore.internBind_cases st tag ty b with he | he | he <;> rw [he] <;>
        exact LsExt.refl _)
    (fun _ _ h => EStore.view_internBind_mono st tag ty b h)
    (EStore.nodeCount_internBind_le st tag ty b)

/-- con-leche: none — arena infrastructure; **the promotion's append extends
the arena** (task #97-P6-2).  This is the conjunct the promotion keeps
outright, where `StoreWF`'s `fresh` is transiently broken. -/
theorem EStore.internPersistent_ext (st : EStore) (w : ENodeView) :
    Ext st (st.internPersistent w).1 :=
  Ext.of_view_mono (by rw [EStore.lss_internPersistent]; exact LsExt.refl _)
    (fun _ _ h => EStore.view_internPersistent_mono st w h)
    (EStore.nodeCount_internPersistent_le st w)

/-! ### The nested interns, lifted

`Monad.lean`'s `internNNode` / `internLNode` / `internLsNode` — task #97-P5-2
§11 item 4's `internNNode`, `internLNode`, `internLsNode` — run through
`EStore.internName` / `internLevel` / `internLevels`, which move the nested
store and leave every expression-level read alone.  The `view` and `scratchOn`
equations below are `rfl`, and are what a caller relating the whole state
wants beside the `Ext`. -/

theorem LStore.internName_ext (st : LStore) (w : NNodeView) :
    LExt st (st.internName w).1 :=
  LExt.of_view_mono (NStore.intern_ext st.ns w) (fun _ _ h => h) (Nat.le_refl _)

theorem LStore.internNamePersistent_ext (st : LStore) (w : NNodeView) :
    LExt st (st.internNamePersistent w).1 :=
  LExt.of_view_mono (NStore.internPersistent_ext st.ns w) (fun _ _ h => h)
    (Nat.le_refl _)

theorem LsStore.internName_ext (st : LsStore) (w : NNodeView) :
    LsExt st (st.internName w).1 :=
  LsExt.of_view_mono (LStore.internName_ext st.ls w) (fun _ _ h => h)

theorem LsStore.internNamePersistent_ext (st : LsStore) (w : NNodeView) :
    LsExt st (st.internNamePersistent w).1 :=
  LsExt.of_view_mono (LStore.internNamePersistent_ext st.ls w) (fun _ _ h => h)

theorem LsStore.internLevel_ext (st : LsStore) (w : LNodeView) :
    LsExt st (st.internLevel w).1 :=
  LsExt.of_view_mono (LStore.intern_ext st.ls w) (fun _ _ h => h)

theorem LsStore.internLevelPersistent_ext (st : LsStore) (w : LNodeView) :
    LsExt st (st.internLevelPersistent w).1 :=
  LsExt.of_view_mono (LStore.internPersistent_ext st.ls w) (fun _ _ h => h)

/-- con-leche: none — arena infrastructure; `Monad.lean`'s `internNNode`
extends the arena. -/
theorem EStore.internName_ext (st : EStore) (w : NNodeView) :
    Ext st (st.internName w).1 :=
  Ext.of_view_mono (LsStore.internName_ext st.lss w) (fun _ _ h => h)
    (Nat.le_refl _)

theorem EStore.internNamePersistent_ext (st : EStore) (w : NNodeView) :
    Ext st (st.internNamePersistent w).1 :=
  Ext.of_view_mono (LsStore.internNamePersistent_ext st.lss w) (fun _ _ h => h)
    (Nat.le_refl _)

/-- con-leche: none — arena infrastructure; `Monad.lean`'s `internLNode`
extends the arena. -/
theorem EStore.internLevel_ext (st : EStore) (w : LNodeView) :
    Ext st (st.internLevel w).1 :=
  Ext.of_view_mono (LsStore.internLevel_ext st.lss w) (fun _ _ h => h)
    (Nat.le_refl _)

theorem EStore.internLevelPersistent_ext (st : EStore) (w : LNodeView) :
    Ext st (st.internLevelPersistent w).1 :=
  Ext.of_view_mono (LsStore.internLevelPersistent_ext st.lss w) (fun _ _ h => h)
    (Nat.le_refl _)

/-- con-leche: none — arena infrastructure; `Monad.lean`'s `internLsNode`
extends the arena. -/
theorem EStore.internLevels_ext (st : EStore) (w : LsNodeView) :
    Ext st (st.internLevels w).1 :=
  Ext.of_view_mono (LsStore.intern_ext st.lss w) (fun _ _ h => h) (Nat.le_refl _)

theorem EStore.internLevelsPersistent_ext (st : EStore) (w : LsNodeView) :
    Ext st (st.internLevelsPersistent w).1 :=
  Ext.of_view_mono (LsStore.internPersistent_ext st.lss w) (fun _ _ h => h)
    (Nat.le_refl _)


theorem EStore.scratchOn_internNamePersistent (st : EStore) (w : NNodeView) :
    (st.internNamePersistent w).1.scratchOn = st.scratchOn := rfl
theorem EStore.scratchOn_internLevelPersistent (st : EStore) (w : LNodeView) :
    (st.internLevelPersistent w).1.scratchOn = st.scratchOn := rfl
theorem EStore.scratchOn_internLevelsPersistent (st : EStore) (w : LsNodeView) :
    (st.internLevelsPersistent w).1.scratchOn = st.scratchOn := rfl


end ConRon.Arena

/-! ## The nested interns' persistence, with the scratch tier off
(task #97-P3-Frontend-2, round 2)

`EStore.intern_isPersistent_of_off` above says *the expression intern hands
back a persistent handle when the scratch tier is closed*.  The three nested
stores had no twin, and `Bridge/Frontend/Chunks.lean`'s `StateD_init_run`
needs two of them: `StateD.init` interns `Name.anonymous` and `Level.zero`
into the tables the whole parse then reads, and `PersStateD` — the clause
behind the fold theorems' `hpd`, without which the fold's first
`dropScratch` makes the stream undecodable — is about exactly those handles.

Each is `{N,L,Ls}Store.intern_view_spec`'s `else` branch and nothing else: the
cons-table hit gives persistence from the `consP` clause it is characterised
by, and the append gives it from the tier word `push` is called at
(`Idx.tierP`).  Neither assumes `ViewOK`, for the reason the expression one
records: persistence is a property of the HANDLE, not of the node.

This section is append-only by construction (see the module note's convention
for concurrent rounds).
-/

namespace ConRon.Arena

end ConRon.Arena

/-! ## The EMPTY arena is well formed (task #97-P3-Frontend-2, round 2)

`Arena/Main.lean`'s `runPipeline` starts at `AState.init EStore.empty`, so the
byte-level capstone at the SEAM (`Bridge/Frontend/Capstone.lean`'s
`Arena.no_False_declaration_pipeline`) needs the invariant there and nowhere
else.  Every clause is vacuous: no tier holds a node, so `view` is `none` at
every handle and `find?` is `none` at every node view, and the counters, the
capacities and the `Sized` clauses are about empty arrays.
-/

namespace ConRon.Arena

@[simp] theorem NStore.pers_empty : (NStore.empty).pers = NTables.empty := rfl
@[simp] theorem NStore.scr_empty : (NStore.empty).scr = NTables.empty := rfl
@[simp] theorem NStore.scratchOn_empty : (NStore.empty).scratchOn = false := rfl

@[simp] theorem NStore.view_empty (i : NIdx) : (NStore.empty).view i = none := by
  simp only [NStore.view, NStore.pers_empty, NStore.scratchOn_empty,
    NTables.get_empty]
  split <;> simp

theorem NStore.empty_wf : NStoreWF NStore.empty := by
  refine ⟨fun _ => 0, ?_⟩
  constructor <;> intros <;>
    simp_all [NTables.find?_empty, NTables.Sized_empty,
      NTables.sizeOf_empty, Idx.idxCap]

@[simp] theorem LStore.pers_empty : (LStore.empty).pers = LTables.empty := rfl
@[simp] theorem LStore.scr_empty : (LStore.empty).scr = LTables.empty := rfl
@[simp] theorem LStore.scratchOn_empty : (LStore.empty).scratchOn = false := rfl
@[simp] theorem LStore.ns_empty : (LStore.empty).ns = NStore.empty := rfl

@[simp] theorem LStore.view_empty (i : LIdx) : (LStore.empty).view i = none := by
  simp only [LStore.view, LStore.pers_empty, LStore.scratchOn_empty,
    LTables.get_empty]
  split <;> simp

theorem LStore.empty_wf : LStoreWF LStore.empty := by
  refine ⟨fun _ => 0, ?_⟩
  constructor <;> intros <;>
    simp_all [LTables.find?_empty, LTables.Sized_empty,
      LTables.sizeOf_empty, Idx.idxCap, NStore.empty_wf]

@[simp] theorem LsStore.pers_empty : (LsStore.empty).pers = LsTables.empty := rfl
@[simp] theorem LsStore.scr_empty : (LsStore.empty).scr = LsTables.empty := rfl
@[simp] theorem LsStore.scratchOn_empty : (LsStore.empty).scratchOn = false := rfl
@[simp] theorem LsStore.ls_empty : (LsStore.empty).ls = LStore.empty := rfl

@[simp] theorem LsStore.view_empty (i : LsIdx) : (LsStore.empty).view i = none := by
  simp only [LsStore.view, LsStore.pers_empty, LsStore.scratchOn_empty,
    LsTables.get_empty]
  split <;> simp

theorem LsStore.empty_wf : LsStoreWF LsStore.empty := by
  constructor <;> intros <;>
    simp_all [LsTables.find?_empty, LsTables.Sized_empty,
      LsTables.sizeOf_empty, Idx.idxCap, LStore.empty_wf]

@[simp] theorem EStore.pers_empty : (EStore.empty).pers = ETables.empty := rfl
@[simp] theorem EStore.scr_empty : (EStore.empty).scr = ETables.empty := rfl
@[simp] theorem EStore.scratchOn_empty : (EStore.empty).scratchOn = false := rfl
@[simp] theorem EStore.lss_empty : (EStore.empty).lss = LsStore.empty := rfl

@[simp] theorem EStore.view_empty (i : EIdx) : (EStore.empty).view i = none := by
  simp only [EStore.view, EStore.pers_empty, EStore.scr_empty, EStore.scratchOn_empty,
    ETables.get_empty]
  split <;> simp

/-- con-leche: none — arena infrastructure; **the empty arena is well
formed**.  This is the invariant `Arena/Main.lean`'s `runPipeline` starts
from, and the one `Bridge/Frontend/Capstone.lean`'s seam letter needs. -/
@[simp] theorem EStore.persFind?_empty (v : ENodeView) :
    (EStore.empty).persFind? v = none := by
  simp only [EStore.persFind?, EStore.pers_empty, ETables.find?_empty]

@[simp] theorem EStore.scrFind?_empty (v : ENodeView) :
    (EStore.empty).scrFind? v = none := by
  simp only [EStore.scrFind?, EStore.scr_empty, ETables.find?_empty]

theorem EStore.empty_wf : StoreWF EStore.empty := by
  refine ⟨fun _ => 0, ?_⟩
  constructor <;> intros <;>
    simp_all [ETables.Sized_empty,
      ETables.sizeOf_empty, Idx.idxCap, LsStore.empty_wf]

end ConRon.Arena


/-! ## The nested interns keep the arena well formed (task #97-P5-Specs round 2)

`Monad.lean`'s `internNNode` / `internLNode` / `internLsNode` run through
`EStore.internName` / `internLevel` / `internLevels`, which move ONE nested
store and leave every level above it alone.  The `Ext` half of that was
already here; what `Refine2/AbsState.lean`'s `storeWF` clause (finding 16)
needs is the `StoreWF` half, and it is the same three observations at each
level: the outer tables do not move, the nested `view` only grows
(`*.view_intern_mono`), and the nested `derived` does not move at a handle
that already decodes — which is the one genuinely new lemma here
(`*.derived_intern_eq`), and is what `derExact` wants because the outer
`derOfView` reads the nested store's derived column.

This section is append-only by construction (see the module note's convention
for concurrent rounds).
-/

namespace ConRon.Arena


theorem NStore.derived_congr {st st' : NStore} {i : NIdx} {v : NNodeView}
    (hv : st.view i = some v) (hon : st'.scratchOn = st.scratchOn)
    (hp : ∀ j x, st.pers.get j = some x → st'.pers.derAt j = st.pers.derAt j)
    (hs : ∀ j x, st.scr.get j = some x → st'.scr.derAt j = st.scr.derAt j) :
    st'.derived i = st.derived i := by
  simp only [NStore.derived, hon]
  split
  · rename_i hpp; exact hp i v (by rw [← NStore.view_pers hpp]; exact hv)
  · rename_i hpp
    split
    · rename_i hoc
      exact hs i v (by rw [← NStore.view_scr (by simpa using hpp) hoc]; exact hv)
    · rfl

/-! ## The nested name intern keeps the arena well formed -/

/-! ## The nested level intern keeps the arena well formed -/

theorem LStore.derived_congr {st st' : LStore} {i : LIdx} {v : LNodeView}
    (hv : st.view i = some v) (hon : st'.scratchOn = st.scratchOn)
    (hp : ∀ j x, st.pers.get j = some x → st'.pers.derAt j = st.pers.derAt j)
    (hs : ∀ j x, st.scr.get j = some x → st'.scr.derAt j = st.scr.derAt j) :
    st'.derived i = st.derived i := by
  simp only [LStore.derived, hon]
  split
  · rename_i hpp; exact hp i v (by rw [← LStore.view_pers hpp]; exact hv)
  · rename_i hpp
    split
    · rename_i hoc
      exact hs i v (by rw [← LStore.view_scr (by simpa using hpp) hoc]; exact hv)
    · rfl

/-! ## The nested level-list intern keeps the arena well formed -/

theorem LsStore.derived_congr {st st' : LsStore} {i : LsIdx} {v : LsNodeView}
    (hv : st.view i = some v) (hon : st'.scratchOn = st.scratchOn)
    (hp : ∀ j x, st.pers.get j = some x → st'.pers.derAt j = st.pers.derAt j)
    (hs : ∀ j x, st.scr.get j = some x → st'.scr.derAt j = st.scr.derAt j) :
    st'.derived i = st.derived i := by
  simp only [LsStore.derived, hon]
  split
  · rename_i hpp; exact hp i v (by rw [← LsStore.view_pers hpp]; exact hv)
  · rename_i hpp
    split
    · rename_i hoc
      exact hs i v (by rw [← LsStore.view_scr (by simpa using hpp) hoc]; exact hv)
    · rfl

/-! ### ============================================================
    `internPersistent` AT A LIVE SCRATCH TIER — the promote window
    (task #97-P5-Fresh)

Finding 17's ruling, discharged: `fresh` holds only locally
(`Arena/WF.lean`'s section note has the parallel-checking argument), so each
`internPersistent` is stated at the WEAK invariant `…StoreWF'` on both sides.
Everything else about it is `wf_push_pers`'s own argument with three
substitutions:

* the scratch tier no longer has to be empty — `st'.scr = st.scr` and
  `st'.scratchOn = st.scratchOn` replace `scrOff`, so a scratch handle's
  `view` and `derived` simply do not move;
* `childOK`'s persistence conjunct for the NEW node came from `scrOff` (every
  live handle was persistent) and now comes from the added precondition
  `NViewPers w`, which a promotion has by construction — it promotes the
  children first;
* `fresh` is gone from both sides, which is the whole point.

The rank function is `wf_push_pers`'s, unchanged: the new node takes
`st.persCount`, which is above every persistent rank and below the new
`persCount`, and a scratch node's rank is left alone (`rankS` only wants
`< nodeCount`, and `nodeCount` grew). -/

/-- con-leche: none — arena infrastructure; appending a name to the persistent
tier with the SCRATCH TIER LIVE keeps the promote-window invariant. -/
theorem NStore.wf_push_pers' {st st' : NStore} {rk : NIdx → Nat} {w : NNodeView}
    {tb : NTables} {inew : NIdx}
    (h : NWFAt' st rk) (hv : st.ViewOK w) (hp : NViewPers w)
    (hon : st'.scratchOn = st.scratchOn)
    (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    NStoreWF' st' := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (NTables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (NTables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact NTables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact NTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact NTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact NTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact NTables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact NTables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact NTables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact NTables.Sized_push h.sizedP
  have hcounttb : tb.count = st.pers.count + 1 := by rw [← htb]; exact NTables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases NTables.sizeOf_push_cases (t := st.pers) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierP) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capP u
    · rw [h1]; omega
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp'; rw [NStore.view_pers hp', hpers]
  -- the scratch tier does not move, so a scratch handle's view is untouched
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = st.view i := by
    intro i hp'; simp only [NStore.view, hp', hon, hscr, Bool.false_eq_true, ite_false]
  have hnew_none : st.view inew = none := by
    rw [NStore.view_pers hnp]; exact NTables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp']
      exact hmonotb i u (by rwa [NStore.view_pers hp'] at hu)
    · rw [hviewS i (by simpa using hp')]; exact hu
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [NStore.view_pers hp']; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp').trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewS i (by simpa using hp')] at hu; exact Or.inl hu
  have hpc : st'.persCount = st.persCount + 1 := by
    simp only [NStore.persCount, hpers, hcounttb]
  have hnc : st'.nodeCount = st.nodeCount + 1 := by
    simp only [NStore.nodeCount, NStore.persCount, NStore.scrCount, hpers, hscr,
      hcounttb]
    omega
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp' : i.isPersistent = true
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [NStore.derived_pers hp', NStore.derived_pers hp', hpers]
      exact hdertb i u (by rwa [NStore.view_pers hp'] at hu)
    · simp only [NStore.derived, hp', hon, hscr, Bool.false_eq_true, ite_false]
  have hdov : ∀ u : NNodeView, (∀ c ∈ u.children, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u :=
    fun u hu => NStore.derOfView_congr (fun c hc => hder c (hu c hc))
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.persCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.persCount else rk inew)
      = st.persCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, c.isPersistent = true →
      (if (st.view c).isNone = true then st.persCount else rk c) ≤ st.persCount := by
    intro c hcp
    by_cases hc : (st.view c).isSome = true
    · rw [hrkold c hc]
      exact Nat.le_of_lt (h.rankP c hcp hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨fun c => if (st.view c).isNone = true then st.persCount else rk c,
    { childOK := ?childOK, rankP := ?rankP, rankS := ?rankS, consP := ?consP,
      consS := ?consS, derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff }⟩
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv c hc
      have hcp : c.isPersistent = true := hp c hc
      refine ⟨hmoneS c hcs, ?_, fun _ => hcp⟩
      rw [hrkold c hcs, hrknew]
      exact h.rankP c hcp hcs
  case rankP =>
    intro i hip _
    rw [hpc]
    have := hrkle i hip
    omega
  case rankS =>
    intro i hip hi
    rw [hviewS i hip] at hi
    rw [hrkold i hi, hnc]
    have := h.rankS i hip hi
    omega
  case consP =>
    intro u i
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consS =>
    intro u i
    rw [hscr]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
      exact ⟨by rw [hviewS i h2]; exact h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [hviewS i h2] at h1
      exact (h.consS u i).mpr ⟨h1, h2⟩
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv, NStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro hoff; rw [hon] at hoff; rw [hscr]; exact h.scrOff hoff

/-- con-leche: none — arena infrastructure; **`NStore.internPersistent`
preserves the promote-window invariant.**  The `fresh`-free half of finding
17's answer at the name tier. -/
theorem NStore.internPersistent_wf' {st : NStore} {w : NNodeView}
    (h : NStoreWF' st) (hv : st.ViewOK w) (hp : NViewPers w)
    (hcap : st.capOKPersistent w) : NStoreWF' (st.internPersistent w).1 := by
  obtain ⟨rk, h⟩ := h
  simp only [NStore.capOKPersistent] at hcap
  simp only [NStore.internPersistent]
  split
  · exact ⟨rk, h⟩
  · rename_i hfp
    exact NStore.wf_push_pers' h hv hp rfl rfl rfl rfl hcap hfp


/-- con-leche: none — arena infrastructure; appending a level to the
persistent tier with the SCRATCH TIER LIVE keeps the promote-window
invariant.  `NStore.wf_push_pers'`'s argument one tier up; `hsync` is not
needed any more, because the name children's persistence is the added
precondition rather than a consequence of `scrOff`. -/
theorem LStore.wf_push_pers' {st st' : LStore} {rk : LIdx → Nat} {w : LNodeView}
    {tb : LTables} {inew : LIdx}
    (h : LWFAt' st rk) (hv : st.ViewOK w) (hp : LViewPers w)
    (hon : st'.scratchOn = st.scratchOn)
    (hns : st'.ns = st.ns) (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    LStoreWF' st' := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (LTables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (LTables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact LTables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact LTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact LTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨ (i.tag = w.tagOf ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact LTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact LTables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact LTables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact LTables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact LTables.Sized_push h.sizedP
  have hcounttb : tb.count = st.pers.count + 1 := by rw [← htb]; exact LTables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases LTables.sizeOf_push_cases (t := st.pers) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierP) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capP u
    · rw [h1]; omega
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp'; rw [LStore.view_pers hp', hpers]
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = st.view i := by
    intro i hp'; simp only [LStore.view, hp', hon, hscr, Bool.false_eq_true, ite_false]
  have hnew_none : st.view inew = none := by
    rw [LStore.view_pers hnp]; exact LTables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp']
      exact hmonotb i u (by rwa [LStore.view_pers hp'] at hu)
    · rw [hviewS i (by simpa using hp')]; exact hu
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [LStore.view_pers hp']; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp').trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewS i (by simpa using hp')] at hu; exact Or.inl hu
  have hpc : st'.persCount = st.persCount + 1 := by
    simp only [LStore.persCount, hpers, hcounttb]
  have hnc : st'.nodeCount = st.nodeCount + 1 := by
    simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount, hpers, hscr,
      hcounttb]
    omega
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp' : i.isPersistent = true
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [LStore.derived_pers hp', LStore.derived_pers hp', hpers]
      exact hdertb i u (by rwa [LStore.view_pers hp'] at hu)
    · simp only [LStore.derived, hp', hon, hscr, Bool.false_eq_true, ite_false]
  have hdov : ∀ u : LNodeView, (∀ c ∈ u.lchildren, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u :=
    fun u hu => LStore.derOfView_congr (fun c hc => hder c (hu c hc))
      (fun c _ => by rw [hns])
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.persCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.persCount else rk inew)
      = st.persCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, c.isPersistent = true →
      (if (st.view c).isNone = true then st.persCount else rk c) ≤ st.persCount := by
    intro c hcp
    by_cases hc : (st.view c).isSome = true
    · rw [hrkold c hc]
      exact Nat.le_of_lt (h.rankP c hcp hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨fun c => if (st.view c).isNone = true then st.persCount else rk c,
    { ns := by rw [hns]; exact h.ns, childOK := ?childOK, nchildOK := ?nchildOK,
      rankP := ?rankP, rankS := ?rankS, consP := ?consP, consS := ?consS,
      derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff,
      sync := by rw [hon, hns]; exact h.sync }⟩
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv.lvl c hc
      have hcp : c.isPersistent = true := hp.lvl c hc
      refine ⟨hmoneS c hcs, ?_, fun _ => hcp⟩
      rw [hrkold c hcs, hrknew]
      exact h.rankP c hcp hcs
  case nchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hns]; exact h.nchildOK i u hi' c hc
    · exact ⟨by rw [hns]; exact hv.nm c hc, fun _ => hp.nm c hc⟩
  case rankP =>
    intro i hip _
    rw [hpc]
    have := hrkle i hip
    omega
  case rankS =>
    intro i hip hi
    rw [hviewS i hip] at hi
    rw [hrkold i hi, hnc]
    have := h.rankS i hip hi
    omega
  case consP =>
    intro u i
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consS =>
    intro u i
    rw [hscr]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
      exact ⟨by rw [hviewS i h2]; exact h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [hviewS i h2] at h1
      exact (h.consS u i).mpr ⟨h1, h2⟩
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.lvl, LStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro hoff; rw [hon] at hoff; rw [hscr]; exact h.scrOff hoff

/-- con-leche: none — arena infrastructure; **`LStore.internPersistent`
preserves the promote-window invariant.** -/
theorem LStore.internPersistent_wf' {st : LStore} {w : LNodeView}
    (h : LStoreWF' st) (hv : st.ViewOK w) (hp : LViewPers w)
    (hcap : st.capOKPersistent w) : LStoreWF' (st.internPersistent w).1 := by
  obtain ⟨rk, h⟩ := h
  simp only [LStore.capOKPersistent] at hcap
  simp only [LStore.internPersistent]
  split
  · exact ⟨rk, h⟩
  · rename_i hfp
    exact LStore.wf_push_pers' h hv hp rfl rfl rfl rfl rfl hcap hfp


/-- con-leche: none — arena infrastructure; appending a level list to the
persistent tier with the SCRATCH TIER LIVE keeps the promote-window
invariant.  No rank clause at this store (a list node has no `LsIdx`
children), so this is the shortest of the four. -/
theorem LsStore.wf_push_pers' {st st' : LsStore} {w : LsNodeView}
    {tb : LsTables} {inew : LsIdx}
    (h : LsWF' st) (hv : st.ViewOK w) (hp : LsViewPers w)
    (hon : st'.scratchOn = st.scratchOn)
    (hls : st'.ls = st.ls) (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    LsStoreWF' st' := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (LsTables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (LsTables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = LsTag.list := by rw [← hid]; exact LsTables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact LsTables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact LsTables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨ (i.tag = LsTag.list ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact LsTables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact LsTables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact LsTables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact LsTables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact LsTables.Sized_push h.sizedP
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u; rw [← htb, LsTables.sizeOf_push]; omega
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp'; rw [LsStore.view_pers hp', hpers]
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = st.view i := by
    intro i hp'; simp only [LsStore.view, hp', hon, hscr, Bool.false_eq_true, ite_false]
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp']
      exact hmonotb i u (by rwa [LsStore.view_pers hp'] at hu)
    · rw [hviewS i (by simpa using hp')]; exact hu
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [LsStore.view_pers hp']; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp').trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewS i (by simpa using hp')] at hu; exact Or.inl hu
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp' : i.isPersistent = true
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [LsStore.derived_pers hp', LsStore.derived_pers hp', hpers]
      exact hdertb i u (by rwa [LsStore.view_pers hp'] at hu)
    · simp only [LsStore.derived, hp', hon, hscr, Bool.false_eq_true, ite_false]
  have hdov : ∀ u : LsNodeView, st'.derOfView u = st.derOfView u :=
    fun u => LsStore.derOfView_congr u (fun c _ => by rw [hls])
  refine { ls := by rw [hls]; exact h.ls, lchildOK := ?lchildOK, consP := ?consP,
           consS := ?consS, derExact := ?derExact,
           sizedP := ?sizedP, sizedS := ?sizedS, capP := ?capP, capS := ?capS,
           scrOff := ?scrOff, sync := by rw [hon, hls]; exact h.sync }
  case lchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hls]; exact h.lchildOK i u hi' c hc
    · exact ⟨by rw [hls]; exact hv c hc, fun _ => hp c hc⟩
  case consP =>
    intro u i
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consS =>
    intro u i
    rw [hscr]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
      exact ⟨by rw [hviewS i h2]; exact h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [hviewS i h2] at h1
      exact (h.consS u i).mpr ⟨h1, h2⟩
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u, hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u, LsStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro hoff; rw [hon] at hoff; rw [hscr]; exact h.scrOff hoff

/-- con-leche: none — arena infrastructure; **`LsStore.internPersistent`
preserves the promote-window invariant.** -/
theorem LsStore.internPersistent_wf' {st : LsStore} {w : LsNodeView}
    (h : LsStoreWF' st) (hv : st.ViewOK w) (hp : LsViewPers w)
    (hcap : st.capOKPersistent w) : LsStoreWF' (st.internPersistent w).1 := by
  simp only [LsStore.capOKPersistent] at hcap
  simp only [LsStore.internPersistent]
  split
  · exact h
  · rename_i hfp
    exact LsStore.wf_push_pers' h hv hp rfl rfl rfl rfl rfl hcap hfp


/-- con-leche: none — arena infrastructure; appending an expression node to
the persistent tier with the SCRATCH TIER LIVE keeps the promote-window
invariant.  `EStore.wf_push_pers` with `fresh` dropped, `scrOff` replaced by
"the scratch tier does not move", and the three child-persistence facts taken
as the precondition `EViewPers w` instead of read off `scrOff`. -/
theorem EStore.wf_push_pers' {st st' : EStore} {rk : EIdx → Nat} {w : ENodeView}
    {tb : ETables} {inew : EIdx}
    (h : EWFAt' st rk) (hv : st.ViewOK w) (hp : EViewPers w)
    (hon : st'.scratchOn = st.scratchOn)
    (hlss : st'.lss = st.lss) (hscr : st'.scr = st.scr)
    (hpush : st.pers.push w (st.derOfView w) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w = none) :
    StoreWF' st' ∧ st'.view inew = some w ∧ inew.isPersistent = true := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have htb : (st.pers.push w (st.derOfView w) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) Idx.tierP).2 = inew := by rw [hpush]
  -- the appended column, read back
  have hgetnew : tb.get inew = some w := by
    rw [← htb, ← hid]; exact (ETables.push_spec st.pers w _ Idx.tierP htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, (ETables.push_spec st.pers w _ Idx.tierP htr hcap).2]; decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact ETables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact ETables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.get i = some u → tb.get i = some u := by
    intro i u hi; rw [← htb]; exact ETables.get_push_mono _ _ _ _ hi
  have hinvtb : ∀ i u, tb.get i = some u →
      st.pers.get i = some u ∨
        (i.tag = w.tagOf ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact ETables.get_push_inv hi
  have hfindtb : ∀ u, tb.find? u = if w = u then some inew else st.pers.find? u := by
    intro u; rw [← htb, ← hid]; exact ETables.find?_push
  have hdertb : ∀ i u, st.pers.get i = some u → tb.derAt i = st.pers.derAt i := by
    intro i u hi; rw [← htb]; exact ETables.derAt_push_of_get h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact ETables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact ETables.Sized_push h.sizedP
  have hcounttb : tb.count = st.pers.count + 1 := by rw [← htb]; exact ETables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases ETables.sizeOf_push_cases (t := st.pers) (w := w) (v := u)
      (d := st.derOfView w) (tr := Idx.tierP) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capP u
    · rw [h1]; omega
  -- the sub-stores are untouched
  have hns : st'.ns = st.ns := by simp only [EStore.ns, hlss]
  have hls : st'.ls = st.ls := by simp only [EStore.ls, hlss]
  -- the two tiers, as `view` sees them
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.get i := by
    intro i hp'
    rw [EStore.view_pers hp', hpers]
  have hviewPold : ∀ i, i.isPersistent = true →
      st.view i = st.pers.get i := fun i hp' => EStore.view_pers hp'
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = st.view i := by
    intro i hp'
    by_cases hsc : st.scratchOn = true
    · rw [EStore.view_scr hp' (by rw [hon]; exact hsc), EStore.view_scr hp' hsc,
        hscr]
    · have hoff : st.scratchOn = false := by simpa using hsc
      rw [EStore.view_off hp' (by rw [hon]; exact hoff), EStore.view_off hp' hoff]
  have hnew_none : st.view inew = none := by
    rw [hviewPold inew hnp]; exact ETables.get_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp']
      exact hmonotb i u (by rwa [hviewPold i hp'] at hu)
    · rw [hviewS i (by simpa using hp')]; exact hu
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp' : i.isPersistent = true
    · rw [hviewP i hp'] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [hviewPold i hp']; exact h1)
      · exact Or.inr ⟨Idx.eq_of_idxNat (h2.trans htag.symm)
          ((Idx.tier_eq_tierP hp').trans (Idx.tier_eq_tierP hnp).symm)
          (h3.trans hix.symm), h4⟩
    · rw [hviewS i (by simpa using hp')] at hu; exact Or.inl hu
  have hpc : st'.persCount = st.persCount + 1 := by
    simp only [EStore.persCount, hpers, hcounttb]
  have hnc : st'.nodeCount = st.nodeCount + 1 := by
    simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, hpers, hscr,
      hcounttb]
    omega
  have hder : ∀ i, (st.view i).isSome = true → st'.derived i = st.derived i := by
    intro i hi
    by_cases hp' : i.isPersistent = true
    · obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
      rw [EStore.derived_pers hp', EStore.derived_pers hp', hpers]
      exact hdertb i u (by rwa [hviewPold i hp'] at hu)
    · have hp'' : i.isPersistent = false := by simpa using hp'
      simp only [EStore.derived, hp'', hon, hscr, Bool.false_eq_true, ite_false]
  have hdov : ∀ u : ENodeView, (∀ c ∈ u.echildren, (st.view c).isSome = true) →
      st'.derOfView u = st.derOfView u := by
    intro u hu
    refine EStore.derOfView_congr (fun c hc => hder c (hu c hc)) ?_ ?_ ?_ <;>
      intro c _ <;>
      simp only [EStore.nder, EStore.lder, EStore.lsder, hns, hls, hlss]
  have hrkold : ∀ c, (st.view c).isSome = true →
      (if (st.view c).isNone = true then st.persCount else rk c) = rk c := by
    intro c hc
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hc
    rw [hu]; rfl
  have hrknew : (if (st.view inew).isNone = true then st.persCount else rk inew)
      = st.persCount := by rw [hnew_none]; rfl
  have hrkle : ∀ c, c.isPersistent = true →
      (if (st.view c).isNone = true then st.persCount else rk c) ≤ st.persCount := by
    intro c hcp
    by_cases hc : (st.view c).isSome = true
    · rw [hrkold c hc]
      exact Nat.le_of_lt (h.rankP c hcp hc)
    · have hh : st.view c = none := by
        cases hv' : st.view c with
        | none => rfl
        | some u => rw [hv'] at hc; exact absurd rfl hc
      rw [hh]; exact Nat.le_refl _
  refine ⟨?wf, by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
  case wf =>
  refine ⟨fun c => if (st.view c).isNone = true then st.persCount else rk c,
    { lss := ?lss, childOK := ?childOK, nchildOK := ?nchildOK,
      lchildOK := ?lchildOK, lschildOK := ?lschildOK,
      rankP := ?rankP, rankS := ?rankS,
      consP := ?consP, consSof := ?consSof,
      derExact := ?derExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, scrOff := ?scrOff,
      sync := by rw [hon, hlss]; exact h.sync }⟩
  case lss => rw [hlss]; exact h.lss
  case childOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · have hch := h.childOK i u hi' c hc
      refine ⟨hmoneS c hch.1, ?_, hch.2.2⟩
      rw [hrkold c hch.1, hrkold i (by rw [hi']; rfl)]
      exact hch.2.1
    · have hcs : (st.view c).isSome = true := hv.expr c hc
      have hcp : c.isPersistent = true := hp.expr c hc
      refine ⟨hmoneS c hcs, ?_, fun _ => hcp⟩
      rw [hrkold c hcs, hrknew]
      exact h.rankP c hcp hcs
  case nchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hns]; exact h.nchildOK i u hi' c hc
    · exact ⟨by rw [hns]; exact hv.nm c hc, fun _ => hp.nm c hc⟩
  case lchildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hls]; exact h.lchildOK i u hi' c hc
    · exact ⟨by rw [hls]; exact hv.lvl c hc, fun _ => hp.lvl c hc⟩
  case lschildOK =>
    intro i u hi c hc
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hlss]; exact h.lschildOK i u hi' c hc
    · exact ⟨by rw [hlss]; exact hv.lst c hc, fun _ => hp.lst c hc⟩
  case rankP =>
    intro i hip _
    rw [hpc]
    have := hrkle i hip
    omega
  case rankS =>
    intro i hip hi
    rw [hviewS i hip] at hi
    rw [hrkold i hi, hnc]
    have := h.rankS i hip hi
    omega
  case consP =>
    intro u i
    simp only [EStore.persFind?]
    rw [hpers, hfindtb u]
    constructor
    · intro hf
      by_cases hw : w = u
      · rw [ite_eq_left hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [ite_eq_right hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl
          simp only [EStore.persFind?] at hf
          rw [hfp] at hf
          exact absurd hf (by simp)
        rw [ite_eq_right hw]; exact hf
      · rw [ite_eq_left rfl]
  case consSof =>
    intro u i
    have hsf : st'.scrFind? u = st.scrFind? u := by
      simp only [EStore.scrFind?, hscr]
    rw [hsf]
    intro hf
    obtain ⟨h1, h2⟩ := h.consSof u i hf
    exact ⟨by rw [hviewS i h2]; exact h1, h2⟩
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.expr, EStore.derived_pers hnp, hpers, hdernew]
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case scrOff => intro hoff; rw [hon] at hoff; rw [hscr]; exact h.scrOff hoff


/-! ### The three nested promote-interns, lifted

`Arena/Promote.lean`'s `internPersistentN` / `internPersistentL` /
`internPersistentLs` run through `EStore.internNamePersistent` /
`internLevelPersistent` / `internLevelsPersistent`, which move ONE nested
store and leave every level above it alone.  These are the
`EStore.internName_wf` family with `intern` replaced by `internPersistent`,
`StoreWF` by `StoreWF'`, and the extra `…ViewPers` precondition threaded
through. -/

theorem NStore.derived_internPersistent_eq' {st : NStore} (h : NStoreWF' st)
    (w : NNodeView) {i : NIdx} {v : NNodeView} (hi : st.view i = some v) :
    (st.internPersistent w).1.derived i = st.derived i := by
  obtain ⟨rk, hwf⟩ := h
  simp only [NStore.internPersistent]
  split
  · rfl
  · exact NStore.derived_congr hi rfl
      (fun j x hj => NTables.derAt_push_of_get hwf.sizedP hj) (fun j x hj => rfl)

theorem LStore.derived_internPersistent_eq' {st : LStore} (h : LStoreWF' st)
    (w : LNodeView) {i : LIdx} {v : LNodeView} (hi : st.view i = some v) :
    (st.internPersistent w).1.derived i = st.derived i := by
  obtain ⟨rk, hwf⟩ := h
  simp only [LStore.internPersistent]
  split
  · rfl
  · exact LStore.derived_congr hi rfl
      (fun j x hj => LTables.derAt_push_of_get hwf.sizedP hj) (fun j x hj => rfl)

theorem LsStore.derived_internPersistent_eq' {st : LsStore} (h : LsStoreWF' st)
    (w : LsNodeView) {i : LsIdx} {v : LsNodeView} (hi : st.view i = some v) :
    (st.internPersistent w).1.derived i = st.derived i := by
  simp only [LsStore.internPersistent]
  split
  · rfl
  · exact LsStore.derived_congr hi rfl
      (fun j x hj => LsTables.derAt_push_of_get h.sizedP hj) (fun j x hj => rfl)

/-! #### A name, promoted -/

theorem LStore.internNamePersistent_wf' {st : LStore} (h : LStoreWF' st)
    {v : NNodeView} (hv : st.ns.ViewOK v) (hp : NViewPers v)
    (hcap : st.ns.capOKPersistent v) :
    LStoreWF' (st.internNamePersistent v).1 := by
  obtain ⟨rk, hwf⟩ := h
  refine ⟨rk, ?_⟩
  have hns : (st.internNamePersistent v).1.ns = (st.ns.internPersistent v).1 := rfl
  constructor
  case ns => rw [hns]; exact NStore.internPersistent_wf' hwf.ns hv hp hcap
  case childOK => exact hwf.childOK
  case nchildOK =>
    intro i u hi c hc
    refine ⟨?_, (hwf.nchildOK i u hi c hc).2⟩
    rw [hns]
    have := (hwf.nchildOK i u hi c hc).1
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp this
    rw [NStore.view_internPersistent_mono _ _ hx]; rfl
  case rankP => exact hwf.rankP
  case rankS => exact hwf.rankS
  case consP => exact hwf.consP
  case consS => exact hwf.consS
  case derExact =>
    intro i u hi
    have hcongr : (st.internNamePersistent v).1.derOfView u = st.derOfView u := by
      refine LStore.derOfView_congr (fun c _ => rfl) (fun c hc => ?_)
      have hs := (hwf.nchildOK i u hi c hc).1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
      show (st.ns.internPersistent v).1.derived c = st.ns.derived c
      exact NStore.derived_internPersistent_eq' hwf.ns v hx
    show st.derived i = _
    rw [hcongr]
    exact hwf.derExact i u hi
  case sizedP => exact hwf.sizedP
  case sizedS => exact hwf.sizedS
  case capP => exact hwf.capP
  case capS => exact hwf.capS
  case scrOff => exact hwf.scrOff
  case sync => rw [hns, NStore.scratchOn_internPersistent]; exact hwf.sync

theorem LsStore.internNamePersistent_wf' {st : LsStore} (h : LsStoreWF' st)
    {v : NNodeView} (hv : st.ls.ns.ViewOK v) (hp : NViewPers v)
    (hcap : st.ls.ns.capOKPersistent v) :
    LsStoreWF' (st.internNamePersistent v).1 := by
  refine { h with
    ls := LStore.internNamePersistent_wf' h.ls hv hp hcap,
    derExact := ?_ }
  intro i u hi
  have hc : (st.internNamePersistent v).1.derOfView u = st.derOfView u :=
    LsStore.derOfView_congr (st' := (st.internNamePersistent v).1) u (fun c _ => rfl)
  show st.derived i = _
  rw [hc]
  exact h.derExact i u hi

theorem EStore.internNamePersistent_wf' {st : EStore} (h : StoreWF' st)
    {v : NNodeView} (hv : st.ns.ViewOK v) (hp : NViewPers v)
    (hcap : st.ns.capOKPersistent v) :
    StoreWF' (st.internNamePersistent v).1 := by
  obtain ⟨rk, hwf⟩ := h
  have hns : (st.internNamePersistent v).1.ns = (st.ns.internPersistent v).1 := rfl
  refine ⟨rk, { hwf with lss := ?_, nchildOK := ?_, derExact := ?_ }⟩
  · exact LsStore.internNamePersistent_wf' hwf.lss hv hp hcap
  · intro i u hi c hc
    refine ⟨?_, (hwf.nchildOK i u hi c hc).2⟩
    rw [hns]
    have hs := (hwf.nchildOK i u hi c hc).1
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    rw [NStore.view_internPersistent_mono _ _ hx]; rfl
  · intro i u hi
    have hcongr : (st.internNamePersistent v).1.derOfView u = st.derOfView u := by
      refine EStore.derOfView_congr (fun c _ => rfl) (fun c hc => ?_)
        (fun c _ => rfl) (fun c _ => rfl)
      have hs := (hwf.nchildOK i u hi c hc).1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
      show (st.ns.internPersistent v).1.derived c = st.ns.derived c
      obtain ⟨rkl, hl⟩ := hwf.lss.ls
      exact NStore.derived_internPersistent_eq' hl.ns v hx
    show st.derived i = _
    rw [hcongr]
    exact hwf.derExact i u hi

/-! #### A level, promoted -/

theorem LsStore.internLevelPersistent_wf' {st : LsStore} (h : LsStoreWF' st)
    {v : LNodeView} (hv : st.ls.ViewOK v) (hp : LViewPers v)
    (hcap : st.ls.capOKPersistent v) :
    LsStoreWF' (st.internLevelPersistent v).1 := by
  have hls : (st.internLevelPersistent v).1.ls = (st.ls.internPersistent v).1 := rfl
  refine { h with ls := ?_, lchildOK := ?_, derExact := ?_, sync := ?_ }
  · rw [hls]; exact LStore.internPersistent_wf' h.ls hv hp hcap
  · intro i u hi c hc
    refine ⟨?_, (h.lchildOK i u hi c hc).2⟩
    rw [hls]
    have hsm := (h.lchildOK i u hi c hc).1
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsm
    rw [LStore.view_internPersistent_mono _ _ hx]; rfl
  · intro i u hi
    have hc : (st.internLevelPersistent v).1.derOfView u = st.derOfView u := by
      refine LsStore.derOfView_congr (st' := (st.internLevelPersistent v).1) u
        (fun c hcc => ?_)
      have hsm := (h.lchildOK i u hi c hcc).1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsm
      show (st.ls.internPersistent v).1.derived c = st.ls.derived c
      exact LStore.derived_internPersistent_eq' h.ls v hx
    show st.derived i = _
    rw [hc]
    exact h.derExact i u hi
  · rw [hls, LStore.scratchOn_internPersistent]; exact h.sync

theorem EStore.internLevelPersistent_wf' {st : EStore} (h : StoreWF' st)
    {v : LNodeView} (hv : st.ls.ViewOK v) (hp : LViewPers v)
    (hcap : st.ls.capOKPersistent v) :
    StoreWF' (st.internLevelPersistent v).1 := by
  obtain ⟨rk, hwf⟩ := h
  have hls : (st.internLevelPersistent v).1.ls = (st.ls.internPersistent v).1 := rfl
  have hnsE : (st.internLevelPersistent v).1.ns = st.ns :=
    LStore.ns_internPersistent st.ls v
  refine ⟨rk, { hwf with lss := ?_, lchildOK := ?_, nchildOK := ?_, derExact := ?_ }⟩
  · exact LsStore.internLevelPersistent_wf' hwf.lss hv hp hcap
  · intro i u hi c hc
    rw [hnsE]
    exact hwf.nchildOK i u hi c hc
  · intro i u hi c hc
    refine ⟨?_, (hwf.lchildOK i u hi c hc).2⟩
    rw [hls]
    have hsm := (hwf.lchildOK i u hi c hc).1
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsm
    rw [LStore.view_internPersistent_mono _ _ hx]; rfl
  · intro i u hi
    have hcg : (st.internLevelPersistent v).1.derOfView u = st.derOfView u := by
      refine EStore.derOfView_congr (fun c _ => rfl)
        (fun c _ => by
          show (st.ls.internPersistent v).1.ns.derived c = st.ns.derived c
          rw [LStore.ns_internPersistent]; rfl)
        (fun c hcc => ?_) (fun c _ => rfl)
      have hsm := (hwf.lchildOK i u hi c hcc).1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsm
      show (st.ls.internPersistent v).1.derived c = st.ls.derived c
      obtain ⟨rkl, hl⟩ := hwf.lss.ls
      exact LStore.derived_internPersistent_eq' ⟨rkl, hl⟩ v hx
    show st.derived i = _
    rw [hcg]
    exact hwf.derExact i u hi

/-! #### A level list, promoted -/

theorem EStore.internLevelsPersistent_wf' {st : EStore} (h : StoreWF' st)
    {v : LsNodeView} (hv : st.lss.ViewOK v) (hp : LsViewPers v)
    (hcap : st.lss.capOKPersistent v) :
    StoreWF' (st.internLevelsPersistent v).1 := by
  obtain ⟨rk, hwf⟩ := h
  have hlss : (st.internLevelsPersistent v).1.lss = (st.lss.internPersistent v).1 :=
    rfl
  have hlsE : (st.internLevelsPersistent v).1.ls = st.ls :=
    LsStore.ls_internPersistent st.lss v
  have hnsE : (st.internLevelsPersistent v).1.ns = st.ns := by
    show (st.lss.internPersistent v).1.ls.ns = st.lss.ls.ns
    rw [LsStore.ls_internPersistent]
  refine ⟨rk, { hwf with
    lss := ?_, nchildOK := ?_, lchildOK := ?_, lschildOK := ?_,
    derExact := ?_, sync := ?_ }⟩
  · exact LsStore.internPersistent_wf' hwf.lss hv hp hcap
  · intro i u hi c hc
    rw [hnsE]
    exact hwf.nchildOK i u hi c hc
  · intro i u hi c hc
    rw [hlsE]
    exact hwf.lchildOK i u hi c hc
  · intro i u hi c hc
    refine ⟨?_, (hwf.lschildOK i u hi c hc).2⟩
    rw [hlss]
    have hsm := (hwf.lschildOK i u hi c hc).1
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsm
    rw [LsStore.view_internPersistent_mono _ _ hx]; rfl
  · intro i u hi
    have hcg : (st.internLevelsPersistent v).1.derOfView u = st.derOfView u := by
      refine EStore.derOfView_congr (fun c _ => rfl)
        (fun c _ => by
          show (st.lss.internPersistent v).1.ls.ns.derived c = st.ns.derived c
          rw [LsStore.ls_internPersistent]; rfl)
        (fun c _ => by
          show (st.lss.internPersistent v).1.ls.derived c = st.ls.derived c
          rw [LsStore.ls_internPersistent]; rfl)
        (fun c hcc => ?_)
      have hsm := (hwf.lschildOK i u hi c hcc).1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsm
      show (st.lss.internPersistent v).1.derived c = st.lss.derived c
      exact LsStore.derived_internPersistent_eq' hwf.lss v hx
    show st.derived i = _
    rw [hcg]
    exact hwf.derExact i u hi
  · rw [hlss, LsStore.scratchOn_internPersistent]; exact hwf.sync


/-! ### What a promote-intern ANSWERS

Two conjuncts of `Bridge/Promote/StoreP.lean`'s `internPersistent_spec`, at
the weak invariant: the handle is PERSISTENT (which is the whole purpose of
`internPersistent` — a promotion must hand back a handle that survives
`dropScratch`) and it decodes to the view that was interned.  Both split
hit/miss: the hit reads `consP`, the miss reads the push. -/

theorem NStore.internPersistent_pers {st : NStore} (h : NStoreWF' st)
    {w : NNodeView} (hcap : st.pers.find? w = none → st.pers.sizeOf w < Idx.idxCap) :
    ((st.internPersistent w).2).isPersistent = true := by
  obtain ⟨rk, h⟩ := h
  simp only [NStore.internPersistent]
  split
  · rename_i i hf; exact ((h.consP w i).mp hf).2
  · rename_i hf
    show ((st.pers.push w (st.derOfView w) Idx.tierP).2.tier == 0) = true
    rw [(NTables.push_spec st.pers w _ Idx.tierP (by decide) (hcap hf)).2]; decide

theorem NStore.internPersistent_view {st : NStore} (h : NStoreWF' st)
    {w : NNodeView} (hcap : st.pers.find? w = none → st.pers.sizeOf w < Idx.idxCap) :
    (st.internPersistent w).1.view (st.internPersistent w).2 = some w := by
  obtain ⟨rk, h⟩ := h
  simp only [NStore.internPersistent]
  split
  · rename_i i hf; exact ((h.consP w i).mp hf).1
  · rename_i hf
    have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
    have hspec := NTables.push_spec st.pers w (st.derOfView w) Idx.tierP htr (hcap hf)
    have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
      show (_ == 0) = true
      rw [hspec.2]; decide
    simp only [NStore.view]
    rw [ite_eq_left hp]
    exact hspec.1

theorem LStore.internPersistent_pers {st : LStore} (h : LStoreWF' st)
    {w : LNodeView} (hcap : st.pers.find? w = none → st.pers.sizeOf w < Idx.idxCap) :
    ((st.internPersistent w).2).isPersistent = true := by
  obtain ⟨rk, h⟩ := h
  simp only [LStore.internPersistent]
  split
  · rename_i i hf; exact ((h.consP w i).mp hf).2
  · rename_i hf
    show ((st.pers.push w (st.derOfView w) Idx.tierP).2.tier == 0) = true
    rw [(LTables.push_spec st.pers w _ Idx.tierP (by decide) (hcap hf)).2]; decide

theorem LStore.internPersistent_view {st : LStore} (h : LStoreWF' st)
    {w : LNodeView} (hcap : st.pers.find? w = none → st.pers.sizeOf w < Idx.idxCap) :
    (st.internPersistent w).1.view (st.internPersistent w).2 = some w := by
  obtain ⟨rk, h⟩ := h
  simp only [LStore.internPersistent]
  split
  · rename_i i hf; exact ((h.consP w i).mp hf).1
  · rename_i hf
    have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
    have hspec := LTables.push_spec st.pers w (st.derOfView w) Idx.tierP htr (hcap hf)
    have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
      show (_ == 0) = true
      rw [hspec.2]; decide
    simp only [LStore.view]
    rw [ite_eq_left hp]
    exact hspec.1

theorem LsStore.internPersistent_pers {st : LsStore} (h : LsStoreWF' st)
    {w : LsNodeView} (hcap : st.pers.find? w = none → st.pers.sizeOf w < Idx.idxCap) :
    ((st.internPersistent w).2).isPersistent = true := by
  simp only [LsStore.internPersistent]
  split
  · rename_i i hf; exact ((h.consP w i).mp hf).2
  · rename_i hf
    show ((st.pers.push w (st.derOfView w) Idx.tierP).2.tier == 0) = true
    rw [(LsTables.push_spec st.pers w _ Idx.tierP (by decide) (hcap hf)).2]; decide

theorem LsStore.internPersistent_view {st : LsStore} (h : LsStoreWF' st)
    {w : LsNodeView} (hcap : st.pers.find? w = none → st.pers.sizeOf w < Idx.idxCap) :
    (st.internPersistent w).1.view (st.internPersistent w).2 = some w := by
  simp only [LsStore.internPersistent]
  split
  · rename_i i hf; exact ((h.consP w i).mp hf).1
  · rename_i hf
    have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
    have hspec := LsTables.push_spec st.pers w (st.derOfView w) Idx.tierP htr (hcap hf)
    have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
      show (_ == 0) = true
      rw [hspec.2]; decide
    simp only [LsStore.view]
    rw [ite_eq_left hp]
    exact hspec.1


/-! ### The three nested stores, extracted from the weak invariant -/

theorem EWFAt'.lssWF {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    LsStoreWF' st.lss := h.lss

theorem EWFAt'.lsWF {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    LStoreWF' st.ls := h.lss.ls

theorem EWFAt'.nsWF {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    NStoreWF' st.ns := by
  obtain ⟨rkl, hl⟩ := h.lss.ls; exact hl.ns

theorem StoreWF'.lssWF {st : EStore} (h : StoreWF' st) : LsStoreWF' st.lss := by
  obtain ⟨rk, h⟩ := h; exact h.lssWF

theorem StoreWF'.lsWF {st : EStore} (h : StoreWF' st) : LStoreWF' st.ls := by
  obtain ⟨rk, h⟩ := h; exact h.lsWF

theorem StoreWF'.nsWF {st : EStore} (h : StoreWF' st) : NStoreWF' st.ns := by
  obtain ⟨rk, h⟩ := h; exact h.nsWF


/-! ### THE BRACKET CLOSES — `dropScratch` restores `fresh` vacuously

`Arena/Store.lean`'s `internPersistent` note: *"the obligation P3 owes is
stated for the BRACKET: `StoreWF` minus `fresh` is preserved by each
`internPersistent`, and `promote … dropScratch` as a whole takes `StoreWF` to
`StoreWF`"*.  The first half is `wf_push_pers'` above; this is the second, and
it cost **four lines**, because `wf_of_scr_empty` never read a freshness
clause of its INPUT in the first place — it establishes the output's
`fresh`/`consS` from `scr = empty`.  So the four `wf_of_scr_empty`
now take the WEAK invariant (one word each, and not a line of their proofs
moved), and the bracket's closing step is their instance at `dropScratch`.

This is `Bridge/Promote/StoreP.lean`'s `StoreWFP.dropScratch_wf`, discharged
one tier down where it belongs. -/

theorem NStore.dropScratch_wfAt' {st : NStore} {rk : NIdx → Nat} (h : NWFAt' st rk) :
    NWFAt st.dropScratch rk := NStore.wf_of_scr_empty h rfl rfl

theorem LStore.dropScratch_wfAt' {st : LStore} {rk : LIdx → Nat} (h : LWFAt' st rk) :
    LWFAt st.dropScratch rk := by
  obtain ⟨rkn, hn⟩ := h.ns
  exact LStore.wf_of_scr_empty h rfl rfl ⟨rkn, NStore.dropScratch_wfAt' hn⟩
    (fun c hp => NStore.view_dropScratch_pers st.ns hp)
    (fun c hp => NStore.derived_dropScratch_pers st.ns hp) rfl

theorem LsStoreWF'.dropScratch_wf {st : LsStore} (h : LsStoreWF' st) :
    LsStoreWF st.dropScratch := by
  obtain ⟨rkl, hl⟩ := h.ls
  exact LsStore.wf_of_scr_empty h rfl rfl ⟨rkl, LStore.dropScratch_wfAt' hl⟩
    (fun c hp => LStore.view_dropScratch_pers st.ls hp)
    (fun c hp => LStore.derived_dropScratch_pers st.ls hp) rfl

theorem EStore.dropScratch_wfAt' {st : EStore} {rk : EIdx → Nat} (h : EWFAt' st rk) :
    EWFAt st.dropScratch rk := by
  have hlsw : LsWF' st.lss := h.lss
  refine EStore.wf_of_scr_empty h rfl rfl (LsStoreWF'.dropScratch_wf hlsw)
    (fun c hp => NStore.view_dropScratch_pers st.ns hp)
    (fun c hp => LStore.view_dropScratch_pers st.ls hp)
    (fun c hp => LsStore.view_dropScratch_pers st.lss hp)
    (fun c hp => NStore.derived_dropScratch_pers st.ns hp)
    (fun c hp => LStore.derived_dropScratch_pers st.ls hp)
    ?_ rfl
  intro c hp
  show (st.lss.dropScratch).derived c = st.lss.derived c
  rw [LsStore.derived_pers hp, LsStore.derived_pers hp]; rfl

/-- con-leche: none — arena infrastructure; **the promotion bracket's closing
step**: dropping the scratch tier turns the promote-window invariant back into
the store invariant, `fresh` and all. -/
theorem StoreWF'.dropScratch_wf {st : EStore} (h : StoreWF' st) :
    StoreWF st.dropScratch := by
  obtain ⟨rk, h⟩ := h; exact ⟨rk, EStore.dropScratch_wfAt' h⟩


/-! ## THE PROMOTE WINDOW'S NODE APPEND (task #97-P5-Specs round 3)

`EStore.wf_push_pers'` above is the append half of `internPersistent` in the
promote window's invariant; this is the composition: `internPersistent` keeps
`StoreWF'`, and the handle it answers is PERSISTENT and decodes.  (Task #119:
the binder datum, and with it the datum half and task #97-P5-Fresh's second
finding — promoting a datum re-keyed the scratch cons table — are gone.) -/

theorem EStore.internPersistent_of_persFind {st : EStore} {rk : EIdx → Nat}
    (_h : EWFAt' st rk) {w : ENodeView} {i : EIdx} (hf : st.persFind? w = some i) :
    st.internPersistent w = (st, i) := by
  simp only [EStore.persFind?] at hf
  simp only [EStore.internPersistent, hf]

/-- con-leche: none — arena infrastructure; **the promote-intern's spec**, in
the promote window's invariant: the store stays weakly well formed, the handle
decodes to the node interned, and it is PERSISTENT — which is the whole point
of the operation and what the walk above it needs at the next node's
`EViewPers`. -/
theorem EStore.internPersistent_spec' {st : EStore} {w : ENodeView}
    (h : StoreWF' st) (hv : st.ViewOK w) (hp : EViewPers w)
    (hcapN : st.persCapNode w) :
    StoreWF' (st.internPersistent w).1 ∧
      (st.internPersistent w).1.view (st.internPersistent w).2 = some w ∧
      (st.internPersistent w).2.isPersistent = true := by
  obtain ⟨rk, h⟩ := h
  simp only [EStore.persCapNode] at hcapN
  cases hf : st.pers.find? w with
  | some i =>
    have hpf : st.persFind? w = some i := hf
    rw [EStore.internPersistent_of_persFind h hpf]
    exact ⟨⟨rk, h⟩, ((h.consP w i).mp hpf).1, ((h.consP w i).mp hpf).2⟩
  | none =>
    have hun : st.internPersistent w =
        ({ st with pers := (st.pers.push w (st.derOfView w) Idx.tierP).1 },
          (st.pers.push w (st.derOfView w) Idx.tierP).2) := by
      simp only [EStore.internPersistent, hf]
    rw [hun]
    exact EStore.wf_push_pers'
      (st' := { st with pers := (st.pers.push w (st.derOfView w) Idx.tierP).1 })
      (tb := (st.pers.push w (st.derOfView w) Idx.tierP).1)
      (inew := (st.pers.push w (st.derOfView w) Idx.tierP).2)
      h hv hp rfl rfl rfl rfl rfl (hcapN hf) hf

end ConRon.Arena
