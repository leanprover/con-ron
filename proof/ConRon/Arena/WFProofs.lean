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

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the `hashData` computed
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

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the `hashData` computed
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

/-- con-leche: ConLeche/Kernel/Expr.lean:137-140 levelsHash — and
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

/-- con-leche: ConLeche/Kernel/Expr.lean:137-140 levelsHash -/
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

/-- con-leche: none — arena infrastructure; **exactness**: on a well-formed
arena, two handles denoting the same expression are equal.  Precedent:
con-leche's retired `Setlec/Kernel/ArenaWF.lean:2758 denote_inj` (at
94a1cf78). -/
theorem denoteE_inj {st : EStore} (h : StoreWF st) {i j : EIdx} {x : Expr}
    (hi : denoteE st i = some x) (hj : denoteE st j = some x) : i = j := by
  obtain ⟨rk, h⟩ := h
  exact denoteE_inj_at h x i j hi hj

/-! ### The derived word is `ConLeche.Expr.data` of the denotation -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the `data` computed
field, lines 357-402.  **Exactness** of the packed derived word: this is the
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
  | lam x y m ih1 ih2 =>
    intro i hi
    obtain ⟨v, hv⟩ := denoteE_view hi
    rw [denoteE_unfold h hv] at hi
    obtain ⟨t, b, ht, hdt, hdb⟩ := denoteEView_lam hi
    rw [ht] at hv
    rw [h.derExact i _ hv]
    simp [EStore.derOfView, EStore.derOfBindAt, derOfBind, ih1 t hdt, ih2 b hdb,
      Expr.data]
  | forallE x y m ih1 ih2 =>
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

/-! ### The binder arms, resolved

`ETables.get` answers `none` on the two binder tags (task #97-P6-16: a
binder's datum carries its own tier bit, so one tier cannot resolve it).
`getWith` is `get` with that gap plugged by a datum READER: `EStore.view` is
`getWith` at `st.viewBM` under the tier select (`view_pers` / `view_scr`
below), and `get` itself is `getWith` at the reader that answers nothing.  So
each tier lemma is proved once, on `getWith`, and specialises to both. -/

/-- con-leche: none — `ETables.get` with the two binder arms resolved through
a datum reader (task #97-P6-16).  `EStore.view` is this at `st.viewBM`. -/
def ETables.getWith (t : ETables) (bm : BMIdx → Option ConLeche.BinderMeta)
    (i : EIdx) : Option ENodeView :=
  if ETag.isBind i.tag then
    match t.getBind i with
    | none => none
    | some (ty, b, mi) => (bm mi).map fun m => eBindView i.tag ty b m
  else t.get i

/-- con-leche: none — the handle `mi` names the datum the view `v` carries,
as far as the reader `bm` can see.  A non-binder view names no datum, so the
condition is vacuous there.  This is `EStore.internBMOfView`'s post-condition,
stated (task #97-P6-16). -/
def ENodeView.BMOK (bm : BMIdx → Option ConLeche.BinderMeta) (v : ENodeView)
    (mi : BMIdx) : Prop :=
  ∀ m, v.bmOf = some m → bm mi = some m

/-- con-leche: none — two node views share a CONS KEY: the same constructor
with the same fields, the binder datum compared at the HANDLE the cons table
actually stores rather than at its value (task #97-P6-16). -/
def ETables.consKeyEq (w : ENodeView) (mi : BMIdx) (v : ENodeView) (mj : BMIdx) :
    Bool :=
  match w, v with
  | .lam ty b _, .lam ty' b' _ => ty == ty' && b == b' && mi == mj
  | .forallE ty b _, .forallE ty' b' _ => ty == ty' && b == b' && mi == mj
  | .bvar i, .bvar j => i == j
  | .fvar a b, .fvar a' b' => a == a' && b == b'
  | .sort u, .sort u' => u == u'
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app f' a' => f == f' && a == a'
  | .letE a b c, .letE a' b' c' => a == a' && b == b' && c == c'
  | .lit l, .lit l' => l == l'
  | .proj n i e, .proj n' i' e' => n == n' && i == i' && e == e'
  | _, _ => false

/-- con-leche: none — the tier can index the array `i`'s tag names.  That is
all `derAt` asks of a handle, and both `get` and `getBind` give it. -/
def ETables.Decodes (t : ETables) (i : EIdx) : Prop :=
  (t.get i).isSome = true ∨ (t.getBind i).isSome = true

theorem ETables.get_eq_none_of_isBind {t : ETables} {i : EIdx}
    (hb : ETag.isBind i.tag = true) : t.get i = none := by
  simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at hb
  simp only [ETables.get]
  rcases hb with h | h <;> rw [h] <;>
    simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
      ETag.forallE, ETag.isBind]

theorem ETables.getBind_eq_none_of_not_isBind {t : ETables} {i : EIdx}
    (hb : ETag.isBind i.tag = false) : t.getBind i = none := by
  simp only [ETag.isBind, Bool.or_eq_false_iff] at hb
  simp [ETables.getBind, hb.1, hb.2]

theorem ETables.get_eq_getWith (t : ETables) (i : EIdx) :
    t.get i = t.getWith (fun _ => none) i := by
  simp only [ETables.getWith]
  split
  · rename_i hb
    rw [ETables.get_eq_none_of_isBind hb]
    split <;> simp
  · rfl

theorem ETables.Decodes_of_getWith {t : ETables}
    {bm : BMIdx → Option ConLeche.BinderMeta}
    {i : EIdx} {v : ENodeView} (h : t.getWith bm i = some v) : t.Decodes i := by
  simp only [ETables.getWith] at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · rename_i hb; exact Or.inr (by rw [hb]; rfl)
  · exact Or.inl (by rw [h]; rfl)

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
  · simp at h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hle _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hli _) h
  · rw [eq_of_beq hc]; exact Tbl.map_inv (hpr _) h
  · simp at h

theorem ETables.get_push_inv {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32}
    {i : EIdx} {v : ENodeView} (h : (t.push w d mi tr).1.get i = some v) :
    t.get i = some v ∨ (i.tag = w.tagOf ∧ i.idxNat = t.sizeOf w ∧ v = w) := by
  refine ETables.get_inv (Q := fun tg n v' => tg = w.tagOf ∧ n = t.sizeOf w ∧ v' = w)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
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

theorem ETables.getWith_eq_none_of_size {t : ETables}
    {bm : BMIdx → Option ConLeche.BinderMeta} {w : ENodeView} {i : EIdx}
    (htg : i.tag = w.tagOf) (hix : i.idxNat = t.sizeOf w) :
    t.getWith bm i = none := by
  simp only [ETables.getWith, ETables.get_eq_none_of_size htg hix,
    ETables.getBind_eq_none_of_size htg hix]
  split <;> rfl

theorem ETables.push_tag {t : ETables} {w : ENodeView} {d : UInt64} {mi : BMIdx}
    {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d mi tr).2.tag = w.tagOf := by
  have hn : ((UInt32.ofNat (t.sizeOf w)).toNat) < Idx.idxCap := by
    rw [Idx.idxCap] at hcap ⊢; simp; omega
  cases w <;>
    simp only [ETables.push, ENodeView.tagOf, ETables.sizeOf] at * <;>
    exact Idx.tag_mk _ _ _ (by decide) htr hn

theorem ETables.push_idxNat {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32}
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d mi tr).2.idxNat = t.sizeOf w := by
  cases w <;>
    simp only [ETables.push, ETables.sizeOf] at * <;>
    exact Idx.idxNat_mk _ _ _ (by decide) htr hcap

/-- The cons probe after an append, at the cons KEY: the pushed record is
found exactly by a probe whose fields — the datum's handle included — match
it (task #97-P6-16). -/
theorem ETables.find?_push_gen {t : ETables} {w v : ENodeView} {d : UInt64}
    {mi mj : BMIdx} {tr : UInt32} :
    (t.push w d mi tr).1.find? v mj =
      if ETables.consKeyEq w mi v mj = true then some (t.push w d mi tr).2
      else t.find? v mj := by
  cases w <;> cases v <;>
    simp only [ETables.push, ETables.find?, ETables.consKeyEq, Tbl.find?_push,
      beq_iff_eq, Bool.and_eq_true, BVarNode.mk.injEq, FVarNode.mk.injEq,
      SortNode.mk.injEq, ConstNode.mk.injEq, AppNode.mk.injEq, BindNode.mk.injEq,
      LetNode.mk.injEq, LitNode.mk.injEq, ProjNode.mk.injEq, and_assoc,
      if_false, Bool.false_eq_true]

theorem ETables.find?_push {t : ETables} {w v : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} (hnb : ETag.isBind w.tagOf = false) :
    (t.push w d mi tr).1.find? v mi =
      if w = v then some (t.push w d mi tr).2 else t.find? v mi := by
  rw [ETables.find?_push_gen]
  have hself : ETables.consKeyEq w mi w mi = true := by
    cases w <;> simp [ETables.consKeyEq]
  by_cases hwv : w = v
  · subst hwv; rw [if_pos hself, if_pos rfl]
  · have hne : ¬ (ETables.consKeyEq w mi v mi = true) := by
      revert hwv
      cases w
      case lam _ _ _ =>
        simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hnb
      case forallE _ _ _ =>
        simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hnb
      all_goals (cases v <;> simp [ETables.consKeyEq] <;> grind)
    rw [if_neg hne, if_neg hwv]

/-- A cons key that matches a BINDER view's key matches it at the datum
HANDLE too: the two views are the same constructor, so `w` carries a datum as
well and the handles are equal.  This is what makes the new `bmKeyP`/`bmKeyS`
clauses survive a node append — the one key the append adds is the caller's
own `mi`, which is in `findBM`'s range (task #97-LC finding 3). -/
theorem ETables.consKeyEq_bmOf {w v : ENodeView} {mi mj : BMIdx}
    (hk : ETables.consKeyEq w mi v mj = true) {m : ConLeche.BinderMeta}
    (hb : v.bmOf = some m) : mi = mj ∧ ∃ m', w.bmOf = some m' := by
  cases v
  case lam ty b m' =>
    cases w
    case lam ty2 b2 m2 =>
      simp only [ETables.consKeyEq, Bool.and_eq_true, beq_iff_eq] at hk
      exact ⟨hk.2, ⟨m2, rfl⟩⟩
    all_goals simp [ETables.consKeyEq] at hk
  case forallE ty b m' =>
    cases w
    case forallE ty2 b2 m2 =>
      simp only [ETables.consKeyEq, Bool.and_eq_true, beq_iff_eq] at hk
      exact ⟨hk.2, ⟨m2, rfl⟩⟩
    all_goals simp [ETables.consKeyEq] at hk
  all_goals simp [ENodeView.bmOf] at hb

theorem ETables.sizeOf_push_cases {t : ETables} {w v : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} :
    (t.push w d mi tr).1.sizeOf v = t.sizeOf v ∨
      ((t.push w d mi tr).1.sizeOf v = t.sizeOf w + 1 ∧ t.sizeOf v = t.sizeOf w) := by
  cases w <;> cases v <;>
    simp only [ETables.push, ETables.sizeOf] <;>
    first
      | exact Or.inl trivial
      | exact Or.inr ⟨Tbl.size_push _ _ _ _, trivial⟩

theorem ETables.Sized_push {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32}
    (hs : t.Sized) : (t.push w d mi tr).1.Sized := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
  cases w <;>
    (simp only [ETables.push, ETables.Sized]
     refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
     first | assumption | exact Tbl.Sized_push (by assumption))

theorem ETables.count_push {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} :
    (t.push w d mi tr).1.count = t.count + 1 := by
  cases w <;>
    simp [ETables.push, ETables.count, Tbl.size_push] <;> omega
/-! `ETables.derAt` is a ten-way `if` chain on the same tag as `get`, but
since task #97-P6-16 `get`'s two binder arms answer `none` and a binder
handle decodes through `getBind` instead — the two chains no longer line up,
so each arm of `derAt` is read off once, here, and the dispatch lemmas below
use these instead of splitting both chains at once. -/

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
column-wise agreement transfers.  The hypothesis is `Decodes`, not `get`:
since task #97-P6-16 a binder handle decodes through `getBind`, and its
derived word is read from the same array as ever. -/
theorem ETables.derAt_congr_decodes {t t' : ETables} {i : EIdx}
    (h : t.Decodes i)
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
  rcases h with h | h
  · obtain ⟨v, h⟩ := Option.isSome_iff_exists.mp h
    simp only [ETables.get] at h
    tag_cases h
    · simp only [ETables.derAt_bvar (eq_of_beq hc)]; exact hb _ (Tbl.lt_of_map h)
    · simp only [ETables.derAt_fvar (eq_of_beq hc)]; exact hfv _ (Tbl.lt_of_map h)
    · simp only [ETables.derAt_sort (eq_of_beq hc)]; exact hso _ (Tbl.lt_of_map h)
    · simp only [ETables.derAt_const (eq_of_beq hc)]; exact hco _ (Tbl.lt_of_map h)
    · simp only [ETables.derAt_app (eq_of_beq hc)]; exact hap _ (Tbl.lt_of_map h)
    · simp at h
    · simp only [ETables.derAt_letE (eq_of_beq hc)]; exact hle _ (Tbl.lt_of_map h)
    · simp only [ETables.derAt_lit (eq_of_beq hc)]; exact hli _ (Tbl.lt_of_map h)
    · simp only [ETables.derAt_proj (eq_of_beq hc)]; exact hpr _ (Tbl.lt_of_map h)
    · simp at h
  · obtain ⟨p, h⟩ := Option.isSome_iff_exists.mp h
    simp only [ETables.getBind] at h
    tag_cases h
    · simp only [ETables.derAt_lam (eq_of_beq hc)]; exact hla _ (Tbl.lt_of_map h)
    · simp only [ETables.derAt_forallE (eq_of_beq hc)]; exact hfa _ (Tbl.lt_of_map h)
    · simp at h

theorem ETables.derAt_congr {t t' : ETables} {i : EIdx} {v : ENodeView}
    (h : t.get i = some v)
    (hb : ∀ n, n < t.bvars.size → t'.bvars.derAt n = t.bvars.derAt n)
    (hfv : ∀ n, n < t.fvars.size → t'.fvars.derAt n = t.fvars.derAt n)
    (hso : ∀ n, n < t.sorts.size → t'.sorts.derAt n = t.sorts.derAt n)
    (hco : ∀ n, n < t.consts.size → t'.consts.derAt n = t.consts.derAt n)
    (hap : ∀ n, n < t.apps.size → t'.apps.derAt n = t.apps.derAt n)
    (hla : ∀ n, n < t.lams.size → t'.lams.derAt n = t.lams.derAt n)
    (hfa : ∀ n, n < t.foralls.size → t'.foralls.derAt n = t.foralls.derAt n)
    (_hbm : ∀ n, n < t.bms.size → t'.bms.derAt n = t.bms.derAt n)
    (hle : ∀ n, n < t.lets.size → t'.lets.derAt n = t.lets.derAt n)
    (hli : ∀ n, n < t.lits.size → t'.lits.derAt n = t.lits.derAt n)
    (hpr : ∀ n, n < t.projs.size → t'.projs.derAt n = t.projs.derAt n) :
    t'.derAt i = t.derAt i :=
  ETables.derAt_congr_decodes (Or.inl (by rw [h]; rfl)) hb hfv hso hco hap hla hfa
    hle hli hpr

theorem ETables.derAt_push_of_decodes {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} {i : EIdx} (hs : t.Sized) (h : t.Decodes i) :
    (t.push w d mi tr).1.derAt i = t.derAt i := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
  cases w <;>
    refine ETables.derAt_congr_decodes h ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    intro n hn <;> simp only [ETables.push] <;>
    first | rfl | exact Tbl.derAt_push_of_lt (by assumption) hn

theorem ETables.derAt_push_of_get {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} {i : EIdx} {v : ENodeView} (hs : t.Sized)
    (h : t.get i = some v) :
    (t.push w d mi tr).1.derAt i = t.derAt i :=
  ETables.derAt_push_of_decodes hs (Or.inl (by rw [h]; rfl))

theorem ETables.derAt_push_new {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} (hs : t.Sized) (htr : tr.toNat < 2)
    (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d mi tr).1.derAt (t.push w d mi tr).2 = d := by
  have htag := ETables.push_tag (t := t) (w := w) (d := d) (mi := mi) (tr := tr)
    htr hcap
  have hix := ETables.push_idxNat (t := t) (w := w) (d := d) (mi := mi) (tr := tr)
    htr hcap
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
  cases w <;>
    simp only [ENodeView.tagOf] at htag <;>
    simp only [ETables.sizeOf] at hix <;>
    simp only [ETables.derAt, htag, hix, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE,
      ETag.lit, ETag.proj, beq_self_eq_true, if_true] <;>
    (simp only [ETables.push]; exact Tbl.derAt_push_size (by assumption))

theorem ETables.get_empty (i : EIdx) : (ETables.empty).get i = none := by
  simp [ETables.empty, ETables.get, Tbl.empty, Tbl.node?]

theorem ETables.getBind_empty (i : EIdx) : (ETables.empty).getBind i = none := by
  simp [ETables.empty, ETables.getBind, Tbl.empty, Tbl.node?]

theorem ETables.getWith_empty (bm : BMIdx → Option ConLeche.BinderMeta) (i : EIdx) :
    (ETables.empty).getWith bm i = none := by
  simp only [ETables.getWith, ETables.get_empty, ETables.getBind_empty]
  split <;> rfl

theorem ETables.find?_empty (v : ENodeView) (mi : BMIdx) :
    (ETables.empty).find? v mi = none := by
  cases v <;> simp [ETables.empty, ETables.find?, Tbl.find?_empty]

theorem ETables.sizeOf_empty (v : ENodeView) : (ETables.empty).sizeOf v = 0 := by
  cases v <;> rfl

theorem ETables.count_empty : (ETables.empty).count = 0 := rfl

theorem ETables.Sized_empty : (ETables.empty).Sized :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The expression tier's `get` is monotone in each of its arrays.  The
`by_cases` chain is the tag dispatch, written out because this library
deliberately does not depend on Mathlib (`split_ifs` is a Mathlib tactic). -/
theorem ETables.get_mono {t t' : ETables}
    (hb : ∀ n a, t.bvars.node? n = some a → t'.bvars.node? n = some a)
    (hfv : ∀ n a, t.fvars.node? n = some a → t'.fvars.node? n = some a)
    (hso : ∀ n a, t.sorts.node? n = some a → t'.sorts.node? n = some a)
    (hco : ∀ n a, t.consts.node? n = some a → t'.consts.node? n = some a)
    (hap : ∀ n a, t.apps.node? n = some a → t'.apps.node? n = some a)
    (_hla : ∀ n a, t.lams.node? n = some a → t'.lams.node? n = some a)
    (_hfa : ∀ n a, t.foralls.node? n = some a → t'.foralls.node? n = some a)
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
  by_cases c5 : ETag.isBind i.tag = true
  · rw [if_pos c5] at h; exact absurd h (by simp)
  rw [if_neg c5] at h ⊢
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

theorem ETables.getBind_mono {t t' : ETables}
    (hla : ∀ n a, t.lams.node? n = some a → t'.lams.node? n = some a)
    (hfa : ∀ n a, t.foralls.node? n = some a → t'.foralls.node? n = some a)
    {i : EIdx} {p : EIdx × EIdx × BMIdx} (h : t.getBind i = some p) :
    t'.getBind i = some p := by
  simp only [ETables.getBind] at h ⊢
  by_cases c5 : (i.tag == ETag.lam) = true
  · rw [if_pos c5] at h ⊢; exact Option.map_mono (hla _) h
  rw [if_neg c5] at h ⊢
  by_cases c6 : (i.tag == ETag.forallE) = true
  · rw [if_pos c6] at h ⊢; exact Option.map_mono (hfa _) h
  rw [if_neg c6] at h ⊢
  exact absurd h (by simp)

theorem ETables.get_push_mono (t : ETables) (w : ENodeView) (d : UInt64)
    (mi : BMIdx) (tr : UInt32) {i : EIdx} {v : ENodeView} (h : t.get i = some v) :
    (t.push w d mi tr).1.get i = some v := by
  cases w <;>
    refine ETables.get_mono ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
    intro n a ha <;> simp only [ETables.push] <;>
    first | exact ha | exact Tbl.node?_push ha

theorem ETables.getBind_push_mono (t : ETables) (w : ENodeView) (d : UInt64)
    (mi : BMIdx) (tr : UInt32) {i : EIdx} {p : EIdx × EIdx × BMIdx}
    (h : t.getBind i = some p) : (t.push w d mi tr).1.getBind i = some p := by
  cases w <;>
    refine ETables.getBind_mono ?_ ?_ h <;>
    intro n a ha <;> simp only [ETables.push] <;>
    first | exact ha | exact Tbl.node?_push ha

theorem ETables.getWith_push_mono (t : ETables)
    (bm : BMIdx → Option ConLeche.BinderMeta) (w : ENodeView) (d : UInt64)
    (mi : BMIdx) (tr : UInt32) {i : EIdx} {v : ENodeView}
    (h : t.getWith bm i = some v) : (t.push w d mi tr).1.getWith bm i = some v := by
  simp only [ETables.getWith] at h ⊢
  split at h
  · rename_i hbd
    rw [if_pos hbd]
    split at h
    · exact absurd h (by simp)
    · rename_i p hp
      rw [ETables.getBind_push_mono t w d mi tr hp]
      exact h
  · rename_i hbd
    rw [if_neg hbd]
    exact ETables.get_push_mono t w d mi tr h

/-! ### The binder-datum store under `pushBM`

`pushBM` touches `bms` and nothing else, so every node read of the tier is
literally unchanged; the datum reads grow exactly as any other `Tbl` does. -/

theorem ETables.get_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) (i : EIdx) : (t.pushBM m d tr).1.get i = t.get i := rfl

theorem ETables.getBind_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) (i : EIdx) : (t.pushBM m d tr).1.getBind i = t.getBind i := rfl

theorem ETables.derAt_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) (i : EIdx) : (t.pushBM m d tr).1.derAt i = t.derAt i := rfl

theorem ETables.count_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) : (t.pushBM m d tr).1.count = t.count := rfl

theorem ETables.find?_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) (v : ENodeView) (mi : BMIdx) :
    (t.pushBM m d tr).1.find? v mi = t.find? v mi := by cases v <;> rfl

theorem ETables.sizeOf_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) (v : ENodeView) :
    (t.pushBM m d tr).1.sizeOf v = t.sizeOf v := by cases v <;> rfl

theorem ETables.bms_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) :
    (t.pushBM m d tr).1.bms = t.bms.push ⟨m.pw⟩ d (t.pushBM m d tr).2 := rfl

theorem ETables.bmSize_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) : (t.pushBM m d tr).1.bmSize = t.bmSize + 1 := by
  simp [ETables.bmSize, ETables.pushBM, Tbl.size_push]

theorem ETables.getBM_pushBM_mono {t : ETables} {m m' : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} {i : BMIdx} (h : t.getBM i = some m') :
    (t.pushBM m d tr).1.getBM i = some m' := by
  simp only [ETables.getBM, ETables.bms_pushBM] at h ⊢
  exact Option.map_mono (fun a ha => Tbl.node?_push ha) h

theorem ETables.Sized_pushBM {t : ETables} {m : ConLeche.BinderMeta} {d : UInt64}
    {tr : UInt32} (hs : t.Sized) : (t.pushBM m d tr).1.Sized := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hs
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Tbl.Sized_push h11⟩

theorem ETables.getBM_empty (i : BMIdx) : (ETables.empty).getBM i = none := by
  simp [ETables.empty, ETables.getBM, Tbl.empty, Tbl.node?]

theorem ETables.findBM_empty (m : ConLeche.BinderMeta) :
    (ETables.empty).findBM m = none := by
  simp [ETables.empty, ETables.findBM, Tbl.find?_empty]

theorem ETables.bmSize_empty : (ETables.empty).bmSize = 0 := rfl

theorem ETables.findBM_pushBM (t : ETables) (m m' : ConLeche.BinderMeta)
    (d : UInt64) (tr : UInt32) :
    (t.pushBM m d tr).1.findBM m' =
      if m.pw = m'.pw then some (t.pushBM m d tr).2 else t.findBM m' := by
  simp only [ETables.findBM, ETables.bms_pushBM, Tbl.find?_push, beq_iff_eq,
    BMNode.mk.injEq]

theorem ETables.pushBM_idx (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) : (t.pushBM m d tr).2 = Idx.mk 0 tr (UInt32.ofNat t.bms.size) := rfl

theorem ETables.getBM_pushBM_new {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} (htr : tr.toNat < 2) (hcap : t.bms.size < Idx.idxCap) :
    (t.pushBM m d tr).1.getBM (t.pushBM m d tr).2 = some m := by
  have hix : (t.pushBM m d tr).2.idxNat = t.bms.size := by
    rw [ETables.pushBM_idx]; exact Idx.idxNat_mk _ _ _ (by decide) htr hcap
  simp only [ETables.getBM, ETables.bms_pushBM, hix, Tbl.node?_push_new,
    Option.map_some]

theorem ETables.pushBM_tier {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} (htr : tr.toNat < 2) (hcap : t.bms.size < Idx.idxCap) :
    (t.pushBM m d tr).2.tier = tr := by
  have hn : ((UInt32.ofNat t.bms.size).toNat) < Idx.idxCap := by
    rw [Idx.idxCap] at hcap ⊢; simp; omega
  rw [ETables.pushBM_idx]; exact Idx.tier_mk _ _ _ (by decide) htr hn

theorem ETables.bmDerAt_pushBM_of_lt {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} {n : Nat} (hs : t.bms.Sized) (hn : n < t.bms.size) :
    (t.pushBM m d tr).1.bms.derAt n = t.bms.derAt n := by
  rw [ETables.bms_pushBM]; exact Tbl.derAt_push_of_lt hs hn

theorem ETables.bmDerAt_pushBM_new {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} (hs : t.bms.Sized) (htr : tr.toNat < 2)
    (hcap : t.bms.size < Idx.idxCap) :
    (t.pushBM m d tr).1.bms.derAt (t.pushBM m d tr).2.idxNat = d := by
  have hix : (t.pushBM m d tr).2.idxNat = t.bms.size := by
    rw [ETables.pushBM_idx]; exact Idx.idxNat_mk _ _ _ (by decide) htr hcap
  rw [ETables.bms_pushBM, hix]; exact Tbl.derAt_push_size hs

theorem ETables.pushBM_idxNat {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} (htr : tr.toNat < 2) (hcap : t.bms.size < Idx.idxCap) :
    (t.pushBM m d tr).2.idxNat = t.bms.size := by
  rw [ETables.pushBM_idx]; exact Idx.idxNat_mk _ _ _ (by decide) htr hcap

/-- The datum store has one constructor, so its handles carry tag `0` — the
fact `EWFAt`'s `bmConsP`/`bmConsS` state and every push establishes (task
#97-LC finding 2). -/
theorem ETables.pushBM_tag {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} (htr : tr.toNat < 2) (hcap : t.bms.size < Idx.idxCap) :
    (t.pushBM m d tr).2.tag = 0 := by
  have hn : ((UInt32.ofNat t.bms.size).toNat) < Idx.idxCap := by
    rw [Idx.idxCap] at hcap ⊢; simp; omega
  rw [ETables.pushBM_idx]; exact Idx.tag_mk _ _ _ (by decide) htr hn

/-- The datum store's `get` does NOT dispatch on the tag, so a handle whose
index is the appended one reads the appended datum whatever its tag bits say.
That is exactly why `EWFAt` has to carry `tag = 0` itself. -/
theorem ETables.getBM_pushBM_at_size {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} {i : BMIdx} (hn : i.idxNat = t.bms.size) :
    (t.pushBM m d tr).1.getBM i = some m := by
  simp only [ETables.getBM, ETables.bms_pushBM, Tbl.node?_push_eq, if_pos hn,
    Option.map_some]

theorem ETables.getBM_pushBM_inv {t : ETables} {m mm : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} {i : BMIdx}
    (h : (t.pushBM m d tr).1.getBM i = some mm) :
    t.getBM i = some mm ∨ (i.idxNat = t.bms.size ∧ mm = m) := by
  simp only [ETables.getBM, ETables.bms_pushBM, Tbl.node?_push_eq] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq] at h
    exact Or.inr ⟨hc, h.symm⟩
  · exact Or.inl h

theorem ETables.getBMDer_pushBM_of_lt {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} {i : BMIdx} (hs : t.bms.Sized)
    (hn : i.idxNat < t.bms.size) :
    (t.pushBM m d tr).1.getBMDer i = t.getBMDer i := by
  have hnode : (t.pushBM m d tr).1.bms.node? i.idxNat = t.bms.node? i.idxNat := by
    rw [ETables.bms_pushBM, Tbl.node?_push_eq, if_neg (Nat.ne_of_lt hn)]
  have hder : (t.pushBM m d tr).1.bms.derAt i.idxNat = t.bms.derAt i.idxNat :=
    ETables.bmDerAt_pushBM_of_lt hs hn
  simp only [ETables.getBMDer, hnode, hder]

theorem ETables.getBMDer_pushBM_at_size {t : ETables} {m : ConLeche.BinderMeta}
    {d : UInt64} {tr : UInt32} {i : BMIdx} (hs : t.bms.Sized)
    (hn : i.idxNat = t.bms.size) :
    (t.pushBM m d tr).1.getBMDer i = (d, m.pw.hasParams) := by
  have hnode : (t.pushBM m d tr).1.bms.node? i.idxNat = some ⟨m.pw⟩ := by
    rw [ETables.bms_pushBM, Tbl.node?_push_eq, if_pos hn]
  have hder : (t.pushBM m d tr).1.bms.derAt i.idxNat = d := by
    rw [ETables.bms_pushBM, hn]; exact Tbl.derAt_push_size hs
  simp only [ETables.getBMDer, hnode, hder]

theorem ETables.bmSize_eq (t : ETables) : t.bmSize = t.bms.size := rfl

theorem ETables.bms_Sized {t : ETables} (hs : t.Sized) : t.bms.Sized :=
  hs.2.2.2.2.2.2.2.2.2.2

theorem ETables.getWith_pushBM (t : ETables) (m : ConLeche.BinderMeta) (d : UInt64)
    (tr : UInt32) (bm : BMIdx → Option ConLeche.BinderMeta) (i : EIdx) :
    (t.pushBM m d tr).1.getWith bm i = t.getWith bm i := by
  simp only [ETables.getWith, ETables.get_pushBM, ETables.getBind_pushBM]

/-! ### `view`, as a tier's `getWith` -/

theorem EStore.viewBM_mono_of_pers {st st' : EStore} (hp : st'.pers = st.pers)
    (hs : st'.scratchOn = st.scratchOn)
    (hsc : ∀ i m, st.scr.getBM i = some m → st'.scr.getBM i = some m)
    {i : BMIdx} {m : ConLeche.BinderMeta} (h : st.viewBM i = some m) :
    st'.viewBM i = some m := by
  unfold EStore.viewBM EStore.persGetBM at h ⊢
  split at h
  · rename_i hc; rw [if_pos hc, hp]; exact h
  · rename_i hc
    rw [if_neg hc]
    split at h
    · rename_i hc2; rw [hs, if_pos hc2]; exact hsc i m h
    · exact absurd h (by simp)

/-- The two nested `match`es of `EStore.view` on a binder tag — `viewBindI`
then `viewBM` — collapse into `ETables.getWith`'s single `Option.map`. -/
theorem viewBind_match {α : Type} (o : Option (EIdx × EIdx × BMIdx))
    (bm : BMIdx → Option ConLeche.BinderMeta)
    (f : EIdx → EIdx → ConLeche.BinderMeta → α) :
    (match (match o with
            | none => none
            | some (ty, b, mi) =>
              match bm mi with
              | none => none
              | some m => some (ty, b, m)) with
     | none => none
     | some (ty, b, m) => some (f ty b m))
      = match o with
        | none => none
        | some (ty, b, mi) => (bm mi).map (fun m => f ty b m) := by
  cases o with
  | none => rfl
  | some p =>
    obtain ⟨ty, b, mi⟩ := p
    dsimp only
    cases bm mi <;> rfl

theorem EStore.view_pers {st : EStore} {i : EIdx} (hp : i.isPersistent = true) :
    st.view i = st.pers.getWith st.viewBM i := by
  by_cases hb : ETag.isBind i.tag = true
  · simp only [EStore.view, ETables.getWith, if_pos hb, EStore.viewBind,
      EStore.viewBindI, EStore.persGetBind, hp, if_true]
    exact viewBind_match _ _ _
  · simp only [EStore.view, ETables.getWith, if_neg hb, hp, if_true]

theorem EStore.view_scr {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.view i = st.scr.getWith st.viewBM i := by
  by_cases hb : ETag.isBind i.tag = true
  · simp only [EStore.view, ETables.getWith, if_pos hb, EStore.viewBind,
      EStore.viewBindI, hp, hon, if_false, if_true, Bool.false_eq_true]
    exact viewBind_match _ _ _
  · simp only [EStore.view, ETables.getWith, if_neg hb, hp, hon, if_false, if_true,
      Bool.false_eq_true]

theorem EStore.view_off {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.view i = none := by
  by_cases hb : ETag.isBind i.tag = true
  · simp only [EStore.view, if_pos hb, EStore.viewBind, EStore.viewBindI, hp, hon,
      if_false, Bool.false_eq_true]
  · simp only [EStore.view, if_neg hb, hp, hon, if_false, Bool.false_eq_true]

/-! ### `intern`, in two steps

Task #97-P6-16 split `intern` into the datum's hash-cons and then the node's
at the datum's handle, so every statement about `intern` is the composition
of the same statement about each.  Each step leaves the store in one of three
shapes — untouched, one array of the scratch tier appended to, or one array
of the persistent tier — and the three `*_cases` lemmas below are the only
place `intern`'s `match` chain is taken apart. -/

theorem ETables.getBM_push (t : ETables) (w : ENodeView) (d : UInt64) (mi : BMIdx)
    (tr : UInt32) (i : BMIdx) : (t.push w d mi tr).1.getBM i = t.getBM i := by
  cases w <;> rfl

theorem ETables.getWith_mono_gen {t t' : ETables}
    {bm bm' : BMIdx → Option ConLeche.BinderMeta}
    (hg : ∀ i v, t.get i = some v → t'.get i = some v)
    (hb : ∀ i p, t.getBind i = some p → t'.getBind i = some p)
    (hm : ∀ i m, bm i = some m → bm' i = some m)
    {i : EIdx} {v : ENodeView} (h : t.getWith bm i = some v) :
    t'.getWith bm' i = some v := by
  simp only [ETables.getWith] at h ⊢
  split at h
  · rename_i hbd
    rw [if_pos hbd]
    split at h
    · exact absurd h (by simp)
    · rename_i p hp
      rw [hb _ _ hp]
      exact Option.map_mono (hm _) h
  · rename_i hbd
    rw [if_neg hbd]
    exact hg _ _ h

theorem EStore.viewBM_mono_of_tiers (st st' : EStore)
    (hs : st'.scratchOn = st.scratchOn)
    (hp : ∀ i m, st.pers.getBM i = some m → st'.pers.getBM i = some m)
    (hsc : ∀ i m, st.scr.getBM i = some m → st'.scr.getBM i = some m)
    {i : BMIdx} {m : ConLeche.BinderMeta} (h : st.viewBM i = some m) :
    st'.viewBM i = some m := by
  unfold EStore.viewBM EStore.persGetBM at h ⊢
  split at h
  · rename_i hc; rw [if_pos hc]; exact hp _ _ h
  · rename_i hc
    rw [if_neg hc]
    split at h
    · rename_i hc2; rw [hs, if_pos hc2]; exact hsc _ _ h
    · exact absurd h (by simp)

theorem EStore.view_mono_of_tiers (st st' : EStore)
    (hs : st'.scratchOn = st.scratchOn)
    (hpg : ∀ i v, st.pers.get i = some v → st'.pers.get i = some v)
    (hpb : ∀ i p, st.pers.getBind i = some p → st'.pers.getBind i = some p)
    (hsg : ∀ i v, st.scr.get i = some v → st'.scr.get i = some v)
    (hsb : ∀ i p, st.scr.getBind i = some p → st'.scr.getBind i = some p)
    (hbm : ∀ i m, st.viewBM i = some m → st'.viewBM i = some m)
    {i : EIdx} {v : ENodeView} (h : st.view i = some v) : st'.view i = some v := by
  by_cases hp : i.isPersistent = true
  · rw [EStore.view_pers hp] at h
    rw [EStore.view_pers hp]
    exact ETables.getWith_mono_gen hpg hpb hbm h
  · have hp' : i.isPersistent = false := by simpa using hp
    by_cases hon : st.scratchOn = true
    · rw [EStore.view_scr hp' hon] at h
      rw [EStore.view_scr hp' (by rw [hs]; exact hon)]
      exact ETables.getWith_mono_gen hsg hsb hbm h
    · rw [EStore.view_off hp' (by simpa using hon)] at h
      exact absurd h (by simp)

theorem EStore.internBM_cases (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBM m).1 = st ∨
      (st.internBM m).1 =
        { st with scr := (st.scr.pushBM m (hash m.pw) Idx.tierS).1 } ∨
      (st.internBM m).1 =
        { st with pers := (st.pers.pushBM m (hash m.pw) Idx.tierP).1 } := by
  unfold EStore.internBM
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem EStore.internBMOfView_cases (st : EStore) (w : ENodeView) :
    (st.internBMOfView w).1 = st ∨
      (∃ m : ConLeche.BinderMeta, (st.internBMOfView w).1 =
        { st with scr := (st.scr.pushBM m (hash m.pw) Idx.tierS).1 }) ∨
      (∃ m : ConLeche.BinderMeta, (st.internBMOfView w).1 =
        { st with pers := (st.pers.pushBM m (hash m.pw) Idx.tierP).1 }) := by
  cases w
  case lam _ _ m =>
    rcases EStore.internBM_cases st m with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨m, hh⟩)
    · exact Or.inr (Or.inr ⟨m, hh⟩)
  case forallE _ _ m =>
    rcases EStore.internBM_cases st m with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨m, hh⟩)
    · exact Or.inr (Or.inr ⟨m, hh⟩)
  all_goals exact Or.inl rfl

theorem EStore.internAt_cases (st : EStore) (v : ENodeView) (mi : BMIdx) :
    (st.internAt v mi).1 = st ∨
      (st.internAt v mi).1 =
        { st with scr := (st.scr.push v (st.derOfView v) mi Idx.tierS).1 } ∨
      (st.internAt v mi).1 =
        { st with pers := (st.pers.push v (st.derOfView v) mi Idx.tierP).1 } := by
  unfold EStore.internAt
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem EStore.view_internBM_mono (st : EStore) (m : ConLeche.BinderMeta) {i : EIdx}
    {v : ENodeView} (h : st.view i = some v) : (st.internBM m).1.view i = some v := by
  rcases EStore.internBM_cases st m with he | he | he <;> rw [he]
  · exact h
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => hk
      · exact fun _ _ hk => ETables.getBM_pushBM_mono hk
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => ETables.getBM_pushBM_mono hk
      · exact fun _ _ hk => hk

theorem EStore.view_internBMOfView_mono (st : EStore) (w : ENodeView) {i : EIdx}
    {v : ENodeView} (h : st.view i = some v) :
    (st.internBMOfView w).1.view i = some v := by
  cases w
  case lam _ _ m => exact EStore.view_internBM_mono st m h
  case forallE _ _ m => exact EStore.view_internBM_mono st m h
  all_goals exact h

theorem EStore.view_internAt_mono (st : EStore) (w : ENodeView) (mi : BMIdx) {i : EIdx}
    {v : ENodeView} (h : st.view i = some v) :
    (st.internAt w mi).1.view i = some v := by
  rcases EStore.internAt_cases st w mi with he | he | he <;> rw [he]
  · exact h
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => ETables.get_push_mono _ _ _ _ _ hh
    · exact fun _ _ hh => ETables.getBind_push_mono _ _ _ _ _ hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => hk
      · exact fun _ _ hk => by rw [ETables.getBM_push]; exact hk
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => ETables.get_push_mono _ _ _ _ _ hh
    · exact fun _ _ hh => ETables.getBind_push_mono _ _ _ _ _ hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => by rw [ETables.getBM_push]; exact hk
      · exact fun _ _ hk => hk

theorem EStore.view_intern_mono (st : EStore) (w : ENodeView) {i : EIdx}
    {v : ENodeView} (h : st.view i = some v) : (st.intern w).1.view i = some v := by
  simp only [EStore.intern]
  exact EStore.view_internAt_mono _ w _ (EStore.view_internBMOfView_mono st w h)

theorem EStore.lss_internBMOfView (st : EStore) (w : ENodeView) :
    (st.internBMOfView w).1.lss = st.lss := by
  rcases EStore.internBMOfView_cases st w with he | ⟨m, he⟩ | ⟨m, he⟩ <;> rw [he]

theorem EStore.lss_internAt (st : EStore) (w : ENodeView) (mi : BMIdx) :
    (st.internAt w mi).1.lss = st.lss := by
  rcases EStore.internAt_cases st w mi with he | he | he <;> rw [he]

theorem EStore.lss_intern (st : EStore) (w : ENodeView) :
    (st.intern w).1.lss = st.lss := by
  simp only [EStore.intern]
  rw [EStore.lss_internAt, EStore.lss_internBMOfView]

theorem EStore.nodeCount_internBMOfView (st : EStore) (w : ENodeView) :
    (st.internBMOfView w).1.nodeCount = st.nodeCount := by
  rcases EStore.internBMOfView_cases st w with he | ⟨m, he⟩ | ⟨m, he⟩ <;> rw [he] <;>
    simp [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.count_pushBM]

theorem EStore.nodeCount_internAt_le (st : EStore) (w : ENodeView) (mi : BMIdx) :
    st.nodeCount ≤ (st.internAt w mi).1.nodeCount := by
  rcases EStore.internAt_cases st w mi with he | he | he <;> rw [he]
  · exact Nat.le_refl _
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_push]
    omega
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_push]
    omega

theorem EStore.nodeCount_intern_le (st : EStore) (w : ENodeView) :
    st.nodeCount ≤ (st.intern w).1.nodeCount := by
  simp only [EStore.intern]
  have h1 := EStore.nodeCount_internBMOfView st w
  have h2 := EStore.nodeCount_internAt_le (st.internBMOfView w).1 w
    (st.internBMOfView w).2
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
  | lam ty b m =>
    simp only [EStore.derOfView, EStore.derOfBindAt,
      he ty (by simp [ENodeView.echildren]), he b (by simp [ENodeView.echildren])]
  | forallE ty b m =>
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
(DESIGN §8.3, con-leche's lesson 6).  Since task #97-P6-16 that needs one
word more: a binder's datum carries its own tier bit, so the claim holds of a
persistent binder exactly when its datum is persistent too — which is
`EWFAt.bmChildOK`, and is what the `hbm` hypothesis asks for. -/

theorem ETables.getWith_congr {t : ETables}
    {bm bm' : BMIdx → Option ConLeche.BinderMeta} {i : EIdx}
    (h : ∀ ty b mi, t.getBind i = some (ty, b, mi) → bm' mi = bm mi) :
    t.getWith bm' i = t.getWith bm i := by
  simp only [ETables.getWith]
  split
  · split
    · rfl
    · rename_i ty b mi hp
      first
        | rw [h ty b mi hp]
        | rw [h ty b mi hp.symm]
  · rfl

theorem EStore.view_dropScratch_pers (st : EStore) {i : EIdx}
    (hbm : ∀ ty b mi, st.viewBindI i = some (ty, b, mi) → mi.isPersistent = true)
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i := by
  rw [EStore.view_pers (st := st.dropScratch) hp, EStore.view_pers (st := st) hp]
  show st.pers.getWith st.dropScratch.viewBM i = st.pers.getWith st.viewBM i
  refine ETables.getWith_congr ?_
  intro ty b mi hg
  have hmi : mi.isPersistent = true := by
    refine hbm ty b mi ?_
    simp only [EStore.viewBindI, EStore.persGetBind, hp, if_true]
    exact hg
  simp only [EStore.viewBM, EStore.persGetBM, hmi, if_true]
  rfl

theorem EStore.view_dropScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : st.dropScratch.view i = none :=
  EStore.view_off hp rfl

theorem EStore.view_enableScratch_pers (st : EStore) {i : EIdx}
    (hbm : ∀ ty b mi, st.viewBindI i = some (ty, b, mi) → mi.isPersistent = true)
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i := by
  rw [EStore.view_pers (st := st.enableScratch) hp, EStore.view_pers (st := st) hp]
  show st.pers.getWith st.enableScratch.viewBM i = st.pers.getWith st.viewBM i
  refine ETables.getWith_congr ?_
  intro ty b mi hg
  have hmi : mi.isPersistent = true := by
    refine hbm ty b mi ?_
    simp only [EStore.viewBindI, EStore.persGetBind, hp, if_true]
    exact hg
  simp only [EStore.viewBM, EStore.persGetBM, hmi, if_true]
  rfl

theorem EStore.view_enableScratch_scr (st : EStore) {i : EIdx}
    (hp : i.isPersistent = false) : st.enableScratch.view i = none := by
  rw [EStore.view_scr (st := st.enableScratch) hp rfl]
  exact ETables.getWith_empty _ _

/-- A persistent binder names a persistent datum: `bmChildOK` read at one
handle, which is what the scratch bracket's two `_pers` lemmas ask for. -/
theorem EWFAt.bmPers {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) (i : EIdx)
    (hp : i.isPersistent = true) :
    ∀ ty b mi, st.viewBindI i = some (ty, b, mi) → mi.isPersistent = true :=
  fun ty b mi hh => (h.bmChildOK i ty b mi hh).2.1 hp

theorem EStore.view_dropScratch_pers_wf {st : EStore} (h : StoreWF st) {i : EIdx}
    (hp : i.isPersistent = true) : st.dropScratch.view i = st.view i := by
  obtain ⟨rk, h⟩ := h
  exact EStore.view_dropScratch_pers st (h.bmPers i hp) hp

theorem EStore.view_enableScratch_pers_wf {st : EStore} (h : StoreWF st) {i : EIdx}
    (hp : i.isPersistent = true) : st.enableScratch.view i = st.view i := by
  obtain ⟨rk, h⟩ := h
  exact EStore.view_enableScratch_pers st (h.bmPers i hp) hp

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


/-! ## The scratch bracket, store by store

`enableScratch` and `dropScratch` differ only in the flag they leave behind:
both replace the scratch tier by `empty` and touch nothing persistent.  So
each store gets **one** lemma, `wf_of_scr_empty`, and both operations are
instances of it.  It is stated at an explicit rank — the same rank the store
had — because `denote…_dropScratch` needs that rank to trade the old fuel for
the new one. -/

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
theorem NStore.wf_of_scr_empty {st st' : NStore} {rk : NIdx → Nat} (h : NWFAt st rk)
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
    NWFAt st.dropScratch rk := NStore.wf_of_scr_empty h rfl rfl

theorem NStore.enableScratch_wfAt {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    NWFAt st.enableScratch rk := NStore.wf_of_scr_empty h rfl rfl

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

theorem LStore.wf_of_scr_empty {st st' : LStore} {rk : LIdx → Nat} (h : LWFAt st rk)
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
  exact LStore.wf_of_scr_empty h rfl rfl ⟨rkn, NStore.dropScratch_wfAt hn⟩
    (fun c hp => NStore.view_dropScratch_pers st.ns hp)
    (fun c hp => NStore.derived_dropScratch_pers st.ns hp) rfl

theorem LStore.enableScratch_wfAt {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    LWFAt st.enableScratch rk := by
  obtain ⟨rkn, hn⟩ := h.ns
  exact LStore.wf_of_scr_empty h rfl rfl ⟨rkn, NStore.enableScratch_wfAt hn⟩
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

theorem LsStore.wf_of_scr_empty {st st' : LsStore} (h : LsWF st)
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
  exact LsStore.wf_of_scr_empty h rfl rfl ⟨rkl, LStore.dropScratch_wfAt hl⟩
    (fun c hp => LStore.view_dropScratch_pers st.ls hp)
    (fun c hp => LStore.derived_dropScratch_pers st.ls hp) rfl

theorem LsStore.enableScratch_wf {st : LsStore} (h : LsWF st) :
    LsWF st.enableScratch := by
  obtain ⟨rkl, hl⟩ := h.ls
  exact LsStore.wf_of_scr_empty h rfl rfl ⟨rkl, LStore.enableScratch_wfAt hl⟩
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

/-! ### Expressions -/

/-! ### The binder datum a view names

Since task #97-P6-16 the cons key of a `lam` or `forallE` node is the datum's
HANDLE, not its value, so every cons statement about a binder view has to
travel through `findBM`.  The three lemmas below are that trip, done once:
the datum store's cons table and its decoder are inverse on a well-formed
store (`findBM_of_viewBM` / `viewBM_of_findBM`), and a PERSISTENT binder node
names a datum the persistent tier's table already knows
(`persFindBM_of_view_pers`) — which is what makes the scratch tier droppable. -/

theorem ETables.bmOf_get {t : ETables} {i : EIdx} {v : ENodeView}
    (h : t.get i = some v) : v.bmOf = none := by
  simp only [ETables.get] at h
  tag_cases h <;>
    first
      | (obtain ⟨a, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl)
      | simp at h

theorem ENodeView.bmOf_eBindView (tag : UInt32) (ty b : EIdx)
    (m : ConLeche.BinderMeta) : (eBindView tag ty b m).bmOf = some m := by
  simp only [eBindView]; split <;> rfl

theorem EStore.findBMOfView_eq_findBM (st : EStore) {v : ENodeView}
    {m : ConLeche.BinderMeta} (h : v.bmOf = some m) :
    st.findBMOfView v = st.findBM m := by
  cases v
  case lam ty b m' =>
    simp only [ENodeView.bmOf, Option.some.injEq] at h
    subst h; rfl
  case forallE ty b m' =>
    simp only [ENodeView.bmOf, Option.some.injEq] at h
    subst h; rfl
  all_goals simp [ENodeView.bmOf] at h

theorem EStore.findBMOfView_eq_zero (st : EStore) {v : ENodeView}
    (h : v.bmOf = none) : st.findBMOfView v = some (Idx.ofWord 0) := by
  cases v
  case lam ty b m' => simp [ENodeView.bmOf] at h
  case forallE ty b m' => simp [ENodeView.bmOf] at h
  all_goals rfl

theorem EStore.viewBM_pers {st : EStore} {i : BMIdx} (hp : i.isPersistent = true) :
    st.viewBM i = st.pers.getBM i := by
  simp only [EStore.viewBM, EStore.persGetBM, hp, if_true]

theorem EStore.viewBM_scr {st : EStore} {i : BMIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.viewBM i = st.scr.getBM i := by
  simp only [EStore.viewBM, EStore.persGetBM, hp, hon, Bool.false_eq_true, if_false,
    if_true]

theorem EStore.viewBM_off {st : EStore} {i : BMIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.viewBM i = none := by
  simp only [EStore.viewBM, EStore.persGetBM, hp, hon, Bool.false_eq_true, if_false]

theorem EWFAt.findBM_of_viewBM {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk)
    {mi : BMIdx} {m : ConLeche.BinderMeta} (h0 : mi.tag = 0)
    (hv : st.viewBM mi = some m) :
    st.findBM m = some mi := by
  by_cases hp : mi.isPersistent = true
  · have hf : st.pers.findBM m = some mi := (h.bmConsP m mi).mpr ⟨hv, hp, h0⟩
    simp only [EStore.findBM, EStore.persFindBM, hf]
  · have hp' : mi.isPersistent = false := by simpa using hp
    have hon : st.scratchOn = true := by
      cases hc : st.scratchOn with
      | false => rw [EStore.viewBM_off hp' hc] at hv; exact absurd hv (by simp)
      | true => rfl
    have hf : st.scr.findBM m = some mi := (h.bmConsS m mi).mpr ⟨hv, hp', h0⟩
    have hfp : st.pers.findBM m = none := h.bmFresh m mi hf
    simp only [EStore.findBM, EStore.persFindBM, hfp, hon, if_true, hf]

theorem EWFAt.viewBM_of_findBM {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk)
    {mi : BMIdx} {m : ConLeche.BinderMeta} (hf : st.findBM m = some mi) :
    st.viewBM mi = some m := by
  simp only [EStore.findBM, EStore.persFindBM] at hf
  split at hf
  · rename_i j hj
    rw [← Option.some.inj hf]
    exact ((h.bmConsP m j).mp hj).1
  · split at hf
    · exact ((h.bmConsS m mi).mp hf).1
    · exact absurd hf (by simp)

theorem EWFAt.persFindBM_of_view_pers {st : EStore} {rk : EIdx → Nat}
    (h : EWFAt st rk) {i : EIdx} {v : ENodeView} {m : ConLeche.BinderMeta}
    (hp : i.isPersistent = true) (hv : st.view i = some v) (hm : v.bmOf = some m) :
    ∃ mp, mp.isPersistent = true ∧ st.viewBM mp = some m ∧
      st.pers.findBM m = some mp := by
  rw [EStore.view_pers hp] at hv
  simp only [ETables.getWith] at hv
  split at hv
  · cases hg : st.pers.getBind i with
    | none => rw [hg] at hv; exact absurd hv (by simp)
    | some p =>
      obtain ⟨ty, b, mp⟩ := p
      rw [hg] at hv
      dsimp only at hv
      cases hbm : st.viewBM mp with
      | none => rw [hbm] at hv; exact absurd hv (by simp)
      | some m' =>
        rw [hbm] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        subst hv
        rw [ENodeView.bmOf_eBindView] at hm
        have hmm : m' = m := Option.some.inj hm
        subst hmm
        have hmpP : mp.isPersistent = true := by
          refine (h.bmChildOK i ty b mp ?_).2.1 hp
          simp only [EStore.viewBindI, EStore.persGetBind, hp, if_true]
          exact hg
        have hmp0 : mp.tag = 0 := by
          refine (h.bmChildOK i ty b mp ?_).2.2
          simp only [EStore.viewBindI, EStore.persGetBind, hp, if_true]
          exact hg
        exact ⟨mp, hmpP, hbm, (h.bmConsP _ mp).mpr ⟨hbm, hmpP, hmp0⟩⟩
  · rw [ETables.bmOf_get hv] at hm
    exact absurd hm (by simp)
theorem EStore.viewBindI_pers {st : EStore} {i : EIdx} (hp : i.isPersistent = true) :
    st.viewBindI i = st.pers.getBind i := by
  simp only [EStore.viewBindI, EStore.persGetBind, hp, if_true]

theorem EStore.viewBindI_scr {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = true) : st.viewBindI i = st.scr.getBind i := by
  simp only [EStore.viewBindI, EStore.persGetBind, hp, hon, Bool.false_eq_true,
    if_false, if_true]

theorem EStore.viewBindI_off {st : EStore} {i : EIdx} (hp : i.isPersistent = false)
    (hon : st.scratchOn = false) : st.viewBindI i = none := by
  simp only [EStore.viewBindI, EStore.persGetBind, hp, hon, Bool.false_eq_true,
    if_false]

/-- A decoded view that carries a datum was decoded THROUGH the datum reader:
the tier's binder record is there and the reader answered that very datum. -/
theorem ETables.bmOf_getWith {t : ETables} {bm : BMIdx → Option ConLeche.BinderMeta}
    {i : EIdx} {v : ENodeView} (h : t.getWith bm i = some v)
    {m : ConLeche.BinderMeta} (hm : v.bmOf = some m) :
    ∃ ty b mj, t.getBind i = some (ty, b, mj) ∧ bm mj = some m := by
  simp only [ETables.getWith] at h
  split at h
  · cases hg : t.getBind i with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨ty, b, mj⟩ := p
      rw [hg] at h
      dsimp only at h
      cases hbm : bm mj with
      | none => rw [hbm] at h; exact absurd h (by simp)
      | some m0 =>
        rw [hbm] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        rw [ENodeView.bmOf_eBindView] at hm
        exact ⟨ty, b, mj, rfl, by rw [hbm, hm]⟩
  · rw [ETables.bmOf_get h] at hm; exact absurd hm (by simp)

/-- A handle that decodes to a view carrying a datum puts that datum in
`findBM`'s range — either tier.  This is `persFindBM_of_view_pers` without the
persistence, and it is what says a cons key's datum is REAL. -/
theorem EWFAt.findBM_of_view {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk)
    {i : EIdx} {v : ENodeView} {m : ConLeche.BinderMeta}
    (hv : st.view i = some v) (hm : v.bmOf = some m) :
    ∃ mj, st.findBM m = some mj := by
  by_cases hp : i.isPersistent = true
  · rw [EStore.view_pers hp] at hv
    obtain ⟨ty, b, mj, hg, hbm⟩ := ETables.bmOf_getWith hv hm
    have hvb : st.viewBindI i = some (ty, b, mj) := by
      rw [EStore.viewBindI_pers hp]; exact hg
    exact ⟨mj, h.findBM_of_viewBM (h.bmChildOK i ty b mj hvb).2.2 hbm⟩
  · have hp' : i.isPersistent = false := by simpa using hp
    cases hc : st.scratchOn with
    | false => rw [EStore.view_off hp' hc] at hv; exact absurd hv (by simp)
    | true =>
      rw [EStore.view_scr hp' hc] at hv
      obtain ⟨ty, b, mj, hg, hbm⟩ := ETables.bmOf_getWith hv hm
      have hvb : st.viewBindI i = some (ty, b, mj) := by
        rw [EStore.viewBindI_scr hp' hc]; exact hg
      exact ⟨mj, h.findBM_of_viewBM (h.bmChildOK i ty b mj hvb).2.2 hbm⟩

theorem EStore.wf_of_scr_empty {st st' : EStore} {rk : EIdx → Nat} (h : EWFAt st rk)
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
  -- the datum store, tier by tier
  have hbmP : ∀ j : BMIdx, j.isPersistent = true → st'.viewBM j = st.viewBM j := by
    intro j hj; rw [EStore.viewBM_pers hj, EStore.viewBM_pers hj, hpers]
  have hbmN : ∀ j : BMIdx, j.isPersistent = false → st'.viewBM j = none := by
    intro j hj
    cases hc : st'.scratchOn with
    | false => exact EStore.viewBM_off hj hc
    | true => rw [EStore.viewBM_scr hj hc, hscr]; exact ETables.getBM_empty j
  -- the node store, tier by tier
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp
    rw [EStore.view_pers hp, EStore.view_pers hp, hpers]
    refine ETables.getWith_congr ?_
    intro ty b mi hg
    refine hbmP mi ((h.bmChildOK i ty b mi ?_).2.1 hp)
    rw [EStore.viewBindI_pers hp]; exact hg
  have hviewN : ∀ i, i.isPersistent = false → st'.view i = none := by
    intro i hp
    cases hc : st'.scratchOn with
    | false => exact EStore.view_off hp hc
    | true => rw [EStore.view_scr hp hc, hscr]; exact ETables.getWith_empty _ i
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
  -- the scratch tier's probes are empty
  have hscrFind : ∀ v : ENodeView, st'.scrFind? v = none := by
    intro v
    simp only [EStore.scrFind?, hscr]
    split
    · rfl
    · exact ETables.find?_empty v _
  -- the persistent probe is the old store's
  have hfind : ∀ v : ENodeView, st'.persFind? v = st.persFind? v := by
    intro v
    simp only [EStore.persFind?]
    cases hb : v.bmOf with
    | none =>
      rw [EStore.findBMOfView_eq_zero _ hb, EStore.findBMOfView_eq_zero _ hb, hpers]
    | some m =>
      rw [EStore.findBMOfView_eq_findBM _ hb, EStore.findBMOfView_eq_findBM _ hb]
      have hbm' : st'.findBM m = st.pers.findBM m := by
        simp only [EStore.findBM, EStore.persFindBM, hpers, hscr,
          ETables.findBM_empty]
        cases st.pers.findBM m with
        | none => simp
        | some j => rfl
      rw [hbm', hpers]
      cases hx : st.pers.findBM m with
      | some mp =>
        have hst : st.findBM m = some mp := by
          simp only [EStore.findBM, EStore.persFindBM, hx]
        rw [hst]
      | none =>
        cases hy : st.findBM m with
        | none => rfl
        | some mj =>
          cases hz : st.pers.find? v mj with
          | none => simp only [hz]
          | some i =>
            exfalso
            have hpf : st.persFind? v = some i := by
              simp only [EStore.persFind?, EStore.findBMOfView_eq_findBM _ hb, hy]
              exact hz
            obtain ⟨hv1, hv2⟩ := (h.consP v i).mp hpf
            obtain ⟨mp, _, _, hmp⟩ := h.persFindBM_of_view_pers hv2 hv1 hb
            rw [hx] at hmp; exact absurd hmp (by simp)
  refine { lss := hlssWF, childOK := ?childOK, nchildOK := ?nchildOK,
           lchildOK := ?lchildOK, lschildOK := ?lschildOK, rankP := ?rankP,
           rankS := ?rankS, bmChildOK := ?bmChildOK, consP := ?consP,
           consS := ?consS, fresh := ?fresh, bmConsP := ?bmConsP,
           bmConsS := ?bmConsS, bmFresh := ?bmFresh,
           bmKeyP := ?bmKeyP, bmKeyS := ?bmKeyS,
           derExact := ?derExact, bmDerExact := ?bmDerExact,
           sizedP := ?sizedP, sizedS := ?sizedS,
           capP := ?capP, capS := ?capS, bmCapP := ?bmCapP, bmCapS := ?bmCapS,
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
  case bmChildOK =>
    intro i ty b mi hvb
    by_cases hp : i.isPersistent = true
    · have hvb' : st.viewBindI i = some (ty, b, mi) := by
        rw [EStore.viewBindI_pers hp, ← hpers, ← EStore.viewBindI_pers hp]
        exact hvb
      have hch := h.bmChildOK i ty b mi hvb'
      have hmp : mi.isPersistent = true := hch.2.1 hp
      exact ⟨by rw [hbmP mi hmp]; exact hch.1, fun _ => hmp, hch.2.2⟩
    · exfalso
      have hp' : i.isPersistent = false := by simpa using hp
      cases hc : st'.scratchOn with
      | false => rw [EStore.viewBindI_off hp' hc] at hvb; exact absurd hvb (by simp)
      | true =>
        rw [EStore.viewBindI_scr hp' hc, hscr, ETables.getBind_empty] at hvb
        exact absurd hvb (by simp)
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
  case bmConsP =>
    intro m j
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2, h3⟩ := (h.bmConsP m j).mp hf
      exact ⟨by rw [hbmP j h2]; exact h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact (h.bmConsP m j).mpr ⟨by rw [← hbmP j h2]; exact h1, h2, h3⟩
  case bmConsS =>
    intro m j
    rw [hscr, ETables.findBM_empty]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2, _⟩
    rw [hbmN j h2] at h1; exact absurd h1 (by simp)
  case bmFresh =>
    intro m j hf
    rw [hscr, ETables.findBM_empty] at hf; exact absurd hf (by simp)
  case bmKeyP =>
    intro v mj i hf
    rw [hpers] at hf ⊢
    exact h.bmKeyP v mj i hf
  case bmKeyS =>
    intro v mj i hf
    rw [hscr, ETables.find?_empty] at hf; exact absurd hf (by simp)
  case derExact =>
    intro i v hi
    obtain ⟨hi', hp⟩ := (hiff i v).mp hi
    rw [EStore.derOfView_congr
      (fun c hc => hder c ((h.childOK i v hi' c hc).2.2 hp))
      (fun c hc => hnsd c ((h.nchildOK i v hi' c hc).2 hp))
      (fun c hc => hld c ((h.lchildOK i v hi' c hc).2 hp))
      (fun c hc => hlsd c ((h.lschildOK i v hi' c hc).2 hp)), hder i hp]
    exact h.derExact i v hi'
  case bmDerExact =>
    intro j m hj
    by_cases hp : j.isPersistent = true
    · have hbd : st'.bmDer j = st.bmDer j := by
        simp only [EStore.bmDer, EStore.persGetBMDer, hp, if_true, hpers]
      rw [hbd]
      exact h.bmDerExact j m (by rw [← hbmP j hp]; exact hj)
    · rw [hbmN j (by simpa using hp)] at hj; exact absurd hj (by simp)
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact ETables.Sized_empty
  case capP => rw [hpers]; exact h.capP
  case capS => intro v; rw [hscr, ETables.sizeOf_empty]; exact Nat.zero_le _
  case bmCapP => rw [hpers]; exact h.bmCapP
  case bmCapS => rw [hscr, ETables.bmSize_empty]; exact Nat.zero_le _
  case scrOff => intro _; exact hscr

theorem EStore.dropScratch_wfAt {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    EWFAt st.dropScratch rk := by
  have hlsw : LsWF st.lss := h.lss
  refine EStore.wf_of_scr_empty h rfl rfl (LsStore.dropScratch_wf hlsw)
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
  refine EStore.wf_of_scr_empty h rfl rfl (LsStore.enableScratch_wf hlsw)
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
    refine ⟨v, by rw [EStore.view_dropScratch_pers st (h.bmPers i hp) hp]; exact hv, ?_⟩
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
      exact denoteN_dropScratch_pers hn
        ((h.nchildOK i _ hv n (by simp [ENodeView.nchildren])).2 hp) hp1

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

theorem ETables.push_spec (t : ETables) (w : ENodeView) (d : UInt64) (mi : BMIdx)
    (tr : UInt32) (hnb : ETag.isBind w.tagOf = false)
    (htr : tr.toNat < 2) (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d mi tr).1.get (t.push w d mi tr).2 = some w ∧
      (t.push w d mi tr).2.tier = tr := by
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
  | lam ty b m => simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hnb
  | forallE ty b m =>
    simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hnb
  | letE ty v b =>
    have htg : (ETag.letE : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.isBind, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | lit l =>
    have htg : (ETag.lit : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.isBind, Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]
  | proj n j e =>
    have htg : (ETag.proj : UInt32).toNat < 16 := by decide
    have hn := ofNat_lt_cap hcap
    refine ⟨?_, ?_⟩
    · simp only [ETables.push, ETables.get, Idx.tag_mk _ _ _ htg htr hn,
        Idx.idxNat_mk _ _ _ htg htr hcap]
      simp [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj, ETag.isBind,
        Tbl.node?_push_new]
    · simp only [ETables.push, Idx.tier_mk _ _ _ htg htr hn]

theorem ETables.push_lam_lams (t : ETables) (ty b : EIdx) (m : ConLeche.BinderMeta)
    (d : UInt64) (mi : BMIdx) (tr : UInt32) :
    (t.push (.lam ty b m) d mi tr).1.lams
      = t.lams.push ⟨ty, b, mi⟩ d (t.push (.lam ty b m) d mi tr).2 := rfl

theorem ETables.push_forallE_foralls (t : ETables) (ty b : EIdx)
    (m : ConLeche.BinderMeta) (d : UInt64) (mi : BMIdx) (tr : UInt32) :
    (t.push (.forallE ty b m) d mi tr).1.foralls
      = t.foralls.push ⟨ty, b, mi⟩ d (t.push (.forallE ty b m) d mi tr).2 := rfl

/-- `push_spec` with the two binder arms included: they answer through
`getWith`'s datum reader, and the record the append wrote names exactly the
handle `mi` the caller interned the datum at (task #97-P6-16). -/
theorem ETables.getWith_push_spec (t : ETables)
    (bm : BMIdx → Option ConLeche.BinderMeta) (w : ENodeView) (d : UInt64)
    (mi : BMIdx) (tr : UInt32) (hmi : ENodeView.BMOK bm w mi) (htr : tr.toNat < 2)
    (hcap : t.sizeOf w < Idx.idxCap) :
    (t.push w d mi tr).1.getWith bm (t.push w d mi tr).2 = some w ∧
      (t.push w d mi tr).2.tier = tr := by
  have htag := ETables.push_tag (t := t) (w := w) (d := d) (mi := mi) (tr := tr)
    htr hcap
  have hix := ETables.push_idxNat (t := t) (w := w) (d := d) (mi := mi) (tr := tr)
    htr hcap
  by_cases hnb : ETag.isBind w.tagOf = false
  · have hnb' : ETag.isBind (t.push w d mi tr).2.tag = false := by rw [htag]; exact hnb
    refine ⟨?_, (ETables.push_spec t w d mi tr hnb htr hcap).2⟩
    simp only [ETables.getWith, hnb', Bool.false_eq_true, if_false]
    exact (ETables.push_spec t w d mi tr hnb htr hcap).1
  · cases w
    case lam ty b m =>
      have hmi : bm mi = some m := hmi m rfl
      simp only [ENodeView.tagOf] at htag
      simp only [ETables.sizeOf] at hix hcap
      have hn : ((UInt32.ofNat t.lams.size).toNat) < Idx.idxCap := by
        rw [Idx.idxCap] at hcap ⊢; simp; omega
      refine ⟨?_, ?_⟩
      · have h2 : (t.push (ENodeView.lam ty b m) d mi tr).1.getBind
            (t.push (ENodeView.lam ty b m) d mi tr).2 = some (ty, b, mi) := by
          simp only [ETables.getBind]
          rw [if_pos (by rw [htag]; decide), ETables.push_lam_lams, hix,
            Tbl.node?_push_new]
          rfl
        simp only [ETables.getWith, h2, hmi, Option.map_some, htag, eBindView,
          ETag.isBind, beq_self_eq_true, Bool.true_or, if_true]
      · simp only [ETables.push]
        exact Idx.tier_mk ETag.lam tr (UInt32.ofNat t.lams.size) (by decide) htr hn
    case forallE ty b m =>
      have hmi : bm mi = some m := hmi m rfl
      simp only [ENodeView.tagOf] at htag
      simp only [ETables.sizeOf] at hix hcap
      have hn : ((UInt32.ofNat t.foralls.size).toNat) < Idx.idxCap := by
        rw [Idx.idxCap] at hcap ⊢; simp; omega
      refine ⟨?_, ?_⟩
      · have h2 :
            (t.push (ENodeView.forallE ty b m) d mi tr).1.getBind
              (t.push (ENodeView.forallE ty b m) d mi tr).2 = some (ty, b, mi) := by
          simp only [ETables.getBind]
          rw [if_neg (by rw [htag]; decide), if_pos (by rw [htag]; decide),
            ETables.push_forallE_foralls, hix, Tbl.node?_push_new]
          rfl
        simp only [ETables.getWith, h2, hmi, Option.map_some, htag, eBindView,
          ETag.isBind, ETag.lam, ETag.forallE, beq_self_eq_true, Bool.or_true,
          if_true]
        rw [if_neg (by decide)]
      · simp only [ETables.push]
        exact Idx.tier_mk ETag.forallE tr (UInt32.ofNat t.foralls.size) (by decide)
          htr hn
    all_goals (exfalso; apply hnb; simp only [ENodeView.tagOf]; decide)

/-! ### Inverting an append at a binder tag

`get_push_inv` says what a node decoded from a grown tier was before it grew.
Since task #97-P6-16 the binder tags go through `getBind` and the datum
reader, so the same inversion is done once more there, and `getWith_push_inv`
is the two halves put back together.  The datum handle the appended record
names is the caller's `mi` — which is what `BMOK` pins down. -/

theorem ENodeView.bmOf_of_isBind {v : ENodeView} (h : ETag.isBind v.tagOf = true) :
    ∃ m, v.bmOf = some m := by
  cases v
  case lam _ _ m => exact ⟨m, rfl⟩
  case forallE _ _ m => exact ⟨m, rfl⟩
  all_goals (exfalso; revert h; simp only [ENodeView.tagOf]; decide)

theorem ETables.getBind_push_of_not_isBind {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} (hnb : ETag.isBind w.tagOf = false) (i : EIdx) :
    (t.push w d mi tr).1.getBind i = t.getBind i := by
  cases w
  case lam _ _ _ =>
    simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hnb
  case forallE _ _ _ =>
    simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hnb
  all_goals rfl

theorem ETables.getBind_push_inv {t : ETables} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} {i : EIdx} {ty b : EIdx} {mj : BMIdx}
    (h : (t.push w d mi tr).1.getBind i = some (ty, b, mj)) :
    t.getBind i = some (ty, b, mj) ∨
      (i.tag = w.tagOf ∧ i.idxNat = t.sizeOf w ∧ mj = mi ∧
        ∀ m, w.bmOf = some m → w = eBindView i.tag ty b m) := by
  cases w
  case lam ty0 b0 m0 =>
    simp only [ETables.getBind] at h ⊢
    by_cases hc : (i.tag == ETag.lam) = true
    · rw [if_pos hc] at h ⊢
      rw [ETables.push_lam_lams, Tbl.node?_push_eq] at h
      split at h
      · rename_i hn
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine Or.inr ⟨by rw [eq_of_beq hc]; rfl, by rw [hn]; rfl, rfl, ?_⟩
        intro m hm
        simp only [ENodeView.bmOf, Option.some.injEq] at hm
        subst hm
        rw [eq_of_beq hc]
        simp [eBindView, ETag.lam]
      · exact Or.inl h
    · rw [if_neg hc] at h ⊢
      exact Or.inl h
  case forallE ty0 b0 m0 =>
    simp only [ETables.getBind] at h ⊢
    by_cases hc : (i.tag == ETag.lam) = true
    · rw [if_pos hc] at h ⊢
      exact Or.inl h
    · rw [if_neg hc] at h ⊢
      by_cases hc2 : (i.tag == ETag.forallE) = true
      · rw [if_pos hc2] at h ⊢
        rw [ETables.push_forallE_foralls, Tbl.node?_push_eq] at h
        split at h
        · rename_i hn
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          refine Or.inr ⟨by rw [eq_of_beq hc2]; rfl, by rw [hn]; rfl, rfl, ?_⟩
          intro m hm
          simp only [ENodeView.bmOf, Option.some.injEq] at hm
          subst hm
          rw [eq_of_beq hc2]
          simp [eBindView, ETag.lam, ETag.forallE]
        · exact Or.inl h
      · rw [if_neg hc2] at h; exact absurd h (by simp)
  all_goals (left; rw [← h]; rfl)

theorem ETables.getWith_push_inv {t : ETables}
    {bm : BMIdx → Option ConLeche.BinderMeta} {w : ENodeView} {d : UInt64}
    {mi : BMIdx} {tr : UInt32} {i : EIdx} {v : ENodeView}
    (hmi : ENodeView.BMOK bm w mi)
    (h : (t.push w d mi tr).1.getWith bm i = some v) :
    t.getWith bm i = some v ∨ (i.tag = w.tagOf ∧ i.idxNat = t.sizeOf w ∧ v = w) := by
  by_cases hb : ETag.isBind i.tag = true
  · simp only [ETables.getWith, if_pos hb] at h ⊢
    cases hg : (t.push w d mi tr).1.getBind i with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨ty, b, mj⟩ := p
      rw [hg] at h
      dsimp only at h
      rcases ETables.getBind_push_inv hg with hold | ⟨h1, h2, h3, h4⟩
      · rw [hold]; exact Or.inl h
      · subst h3
        obtain ⟨m0, hm0⟩ := ENodeView.bmOf_of_isBind (by rw [← h1]; exact hb)
        rw [hmi m0 hm0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact Or.inr ⟨h1, h2, by rw [← h]; exact (h4 m0 hm0).symm⟩
  · simp only [ETables.getWith, if_neg hb] at h ⊢
    exact ETables.get_push_inv h

/-- The cons key a probe uses and the view it probes for agree exactly when
the views do: the datum's handle is the datum, because `findBM` and `viewBM`
are inverse on a well-formed store (task #97-P6-16). -/
theorem EWFAt.consKeyEq_iff {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk)
    {w u : ENodeView} {mi mj : BMIdx} (hmi0 : mi.tag = 0)
    (hmi : ENodeView.BMOK st.viewBM w mi)
    (hmj : st.findBMOfView u = some mj) :
    ETables.consKeyEq w mi u mj = true ↔ w = u := by
  cases w
  case lam ty b m =>
    have hbm : st.viewBM mi = some m := hmi m rfl
    cases u
    case lam ty' b' m' =>
      have hmj' : st.findBM m' = some mj := by
        rw [← EStore.findBMOfView_eq_findBM st
          (rfl : (ENodeView.lam ty' b' m').bmOf = some m')]
        exact hmj
      constructor
      · intro hk
        simp only [ETables.consKeyEq, Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
        have hvv := h.viewBM_of_findBM hmj'
        rw [hbm] at hvv
        rw [Option.some.inj hvv]
      · intro he
        simp only [ENodeView.lam.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        have hf := h.findBM_of_viewBM hmi0 hbm
        rw [hf] at hmj'
        have hij : mi = mj := Option.some.inj hmj'
        subst hij
        simp [ETables.consKeyEq]
    all_goals simp [ETables.consKeyEq]
  case forallE ty b m =>
    have hbm : st.viewBM mi = some m := hmi m rfl
    cases u
    case forallE ty' b' m' =>
      have hmj' : st.findBM m' = some mj := by
        rw [← EStore.findBMOfView_eq_findBM st
          (rfl : (ENodeView.forallE ty' b' m').bmOf = some m')]
        exact hmj
      constructor
      · intro hk
        simp only [ETables.consKeyEq, Bool.and_eq_true, beq_iff_eq] at hk
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
        have hvv := h.viewBM_of_findBM hmj'
        rw [hbm] at hvv
        rw [Option.some.inj hvv]
      · intro he
        simp only [ENodeView.forallE.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        have hf := h.findBM_of_viewBM hmi0 hbm
        rw [hf] at hmj'
        have hij : mi = mj := Option.some.inj hmj'
        subst hij
        simp [ETables.consKeyEq]
    all_goals simp [ETables.consKeyEq]
  all_goals (cases u <;> simp [ETables.consKeyEq, and_assoc])

theorem ETables.findBM_push (t : ETables) (w : ENodeView) (d : UInt64) (mi : BMIdx)
    (tr : UInt32) (m : ConLeche.BinderMeta) :
    (t.push w d mi tr).1.findBM m = t.findBM m := by cases w <;> rfl

theorem ETables.getBMDer_push (t : ETables) (w : ENodeView) (d : UInt64) (mi : BMIdx)
    (tr : UInt32) (i : BMIdx) :
    (t.push w d mi tr).1.getBMDer i = t.getBMDer i := by cases w <;> rfl

theorem ETables.bmSize_push (t : ETables) (w : ENodeView) (d : UInt64) (mi : BMIdx)
    (tr : UInt32) : (t.push w d mi tr).1.bmSize = t.bmSize := by cases w <;> rfl

theorem ETables.isBind_of_getBind {t : ETables} {i : EIdx} {p : EIdx × EIdx × BMIdx}
    (h : t.getBind i = some p) : ETag.isBind i.tag = true := by
  simp only [ETables.getBind] at h
  split at h
  · rename_i hc; simp [ETag.isBind, hc]
  · split at h
    · rename_i hc; simp [ETag.isBind, hc]
    · exact absurd h (by simp)

theorem ETables.find?_bmOf_none {t : ETables} {v : ENodeView} (h : v.bmOf = none)
    (mi mj : BMIdx) : t.find? v mi = t.find? v mj := by
  cases v
  case lam _ _ _ => simp [ENodeView.bmOf] at h
  case forallE _ _ _ => simp [ENodeView.bmOf] at h
  all_goals rfl

/-- con-leche: none — arena infrastructure; appending to the scratch tier
keeps `StoreWF`.  Precedent: con-leche's retired
`Setlec/Kernel/IExpr.lean:464 intern` (at 94a1cf78). -/
theorem EStore.wf_push_scr {st st' : EStore} {rk : EIdx → Nat} {w : ENodeView}
    {tb : ETables} {inew : EIdx}
    (h : EWFAt st rk) (hv : st.ViewOK w)
    (hon : st.scratchOn = true) (hon' : st'.scratchOn = true)
    (hlss : st'.lss = st.lss) (hpers : st'.pers = st.pers)
    {mi : BMIdx} (hmi0 : mi.tag = 0) (hmi : ENodeView.BMOK st.viewBM w mi)
    (hpush : st.scr.push w (st.derOfView w) mi Idx.tierS = (tb, inew))
    (hscr : st'.scr = tb)
    (hcap : st.scr.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w mi = none) (hfs : st.scr.find? w mi = none) :
    StoreWF st' ∧ st'.view inew = some w ∧ inew.isPersistent = false := by
  have htr : (Idx.tierS : UInt32).toNat < 2 := by decide
  have htb : (st.scr.push w (st.derOfView w) mi Idx.tierS).1 = tb := by rw [hpush]
  have hid : (st.scr.push w (st.derOfView w) mi Idx.tierS).2 = inew := by rw [hpush]
  -- the datum store is untouched, so `viewBM` and `findBM` do not move
  have hvbm : ∀ j : BMIdx, st'.viewBM j = st.viewBM j := by
    intro j
    by_cases hjp : j.isPersistent = true
    · rw [EStore.viewBM_pers hjp, EStore.viewBM_pers hjp, hpers]
    · have hjp' : j.isPersistent = false := by simpa using hjp
      rw [EStore.viewBM_scr hjp' hon', EStore.viewBM_scr hjp' hon, hscr, ← htb,
        ETables.getBM_push]
  have hfbm : ∀ m : ConLeche.BinderMeta, st'.findBM m = st.findBM m := by
    intro m
    simp only [EStore.findBM, EStore.persFindBM, hpers, hscr, hon, hon', ← htb,
      ETables.findBM_push]
  have hfov : ∀ v : ENodeView, st'.findBMOfView v = st.findBMOfView v := by
    intro v
    cases hb : v.bmOf with
    | none =>
      rw [EStore.findBMOfView_eq_zero _ hb, EStore.findBMOfView_eq_zero _ hb]
    | some m =>
      rw [EStore.findBMOfView_eq_findBM _ hb, EStore.findBMOfView_eq_findBM _ hb,
        hfbm]
  -- `w`'s own probe, at the handle the caller interned its datum at
  have hfovw : ∃ mw, st.findBMOfView w = some mw := by
    cases hb : w.bmOf with
    | none => exact ⟨_, EStore.findBMOfView_eq_zero _ hb⟩
    | some m =>
      exact ⟨mi, by rw [EStore.findBMOfView_eq_findBM _ hb,
        h.findBM_of_viewBM hmi0 (hmi m hb)]⟩
  have hprobe : ∀ (t : ETables) (mw : BMIdx), st.findBMOfView w = some mw →
      t.find? w mw = t.find? w mi := by
    intro t mw hw
    cases hb : w.bmOf with
    | none => exact ETables.find?_bmOf_none hb _ _
    | some m =>
      rw [EStore.findBMOfView_eq_findBM _ hb, h.findBM_of_viewBM hmi0 (hmi m hb)] at hw
      rw [Option.some.inj hw]
  -- the appended column, read back
  have hgetnew : tb.getWith st.viewBM inew = some w := by
    rw [← htb, ← hid]
    exact (ETables.getWith_push_spec st.scr st.viewBM w _ mi Idx.tierS hmi htr hcap).1
  have hnp : inew.isPersistent = false := by
    show (inew.tier == 0) = false
    rw [← hid,
      (ETables.getWith_push_spec st.scr st.viewBM w _ mi Idx.tierS hmi htr hcap).2]
    decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact ETables.push_tag htr hcap
  have hix : inew.idxNat = st.scr.sizeOf w := by
    rw [← hid]; exact ETables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.scr.getWith st.viewBM i = some u →
      tb.getWith st.viewBM i = some u := by
    intro i u hi; rw [← htb]; exact ETables.getWith_push_mono _ _ _ _ _ _ hi
  have hinvtb : ∀ i u, tb.getWith st.viewBM i = some u →
      st.scr.getWith st.viewBM i = some u ∨
        (i.tag = w.tagOf ∧ i.idxNat = st.scr.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact ETables.getWith_push_inv hmi hi
  have hfindtb : ∀ u mj, st.findBMOfView u = some mj →
      tb.find? u mj = if w = u then some inew else st.scr.find? u mj := by
    intro u mj hmj
    rw [← htb, ← hid, ETables.find?_push_gen]
    by_cases hk : ETables.consKeyEq w mi u mj = true
    · rw [if_pos hk, if_pos ((h.consKeyEq_iff hmi0 hmi hmj).mp hk)]
    · rw [if_neg hk, if_neg (fun he => hk ((h.consKeyEq_iff hmi0 hmi hmj).mpr he))]
  have hdertb : ∀ i, st.scr.Decodes i → tb.derAt i = st.scr.derAt i := by
    intro i hi; rw [← htb]; exact ETables.derAt_push_of_decodes h.sizedS hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact ETables.derAt_push_new h.sizedS htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact ETables.Sized_push h.sizedS
  have hcounttb : tb.count = st.scr.count + 1 := by rw [← htb]; exact ETables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases ETables.sizeOf_push_cases (t := st.scr) (w := w) (v := u)
      (d := st.derOfView w) (mi := mi) (tr := Idx.tierS) with h1 | ⟨h1, _⟩
    · rw [h1]; exact h.capS u
    · rw [h1]; omega
  -- the two tiers, as `view` sees them
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = st.view i := by
    intro i hp
    rw [EStore.view_pers hp, EStore.view_pers hp, hpers]
    exact ETables.getWith_congr (fun ty b mj _ => hvbm mj)
  have hviewS : ∀ i, i.isPersistent = false → st'.view i = tb.getWith st.viewBM i := by
    intro i hp
    rw [EStore.view_scr hp hon', hscr]
    exact ETables.getWith_congr (fun ty b mj _ => hvbm mj)
  have hviewSold : ∀ i, i.isPersistent = false →
      st.view i = st.scr.getWith st.viewBM i := fun i hp => EStore.view_scr hp hon
  have hnew_none : st.view inew = none := by
    rw [hviewSold inew hnp]; exact ETables.getWith_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp]; exact hu
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [hviewS i hp']
      exact hmonotb i u (by rwa [hviewSold i hp'] at hu)
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
      · exact Or.inl (by rw [hviewSold i hp']; exact h1)
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
      exact hdertb i (ETables.Decodes_of_getWith (by rwa [hviewSold i hp'] at hu))
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
      rankP := ?rankP, rankS := ?rankS, bmChildOK := ?bmChildOK,
      consP := ?consP, consS := ?consS, fresh := ?fresh,
      bmConsP := ?bmConsP, bmConsS := ?bmConsS, bmFresh := ?bmFresh,
      bmKeyP := ?bmKeyP, bmKeyS := ?bmKeyS,
      derExact := ?derExact, bmDerExact := ?bmDerExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, bmCapP := ?bmCapP,
      bmCapS := ?bmCapS, scrOff := ?scrOff,
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
  case bmChildOK =>
    intro i ty b mj hvb
    by_cases hp : i.isPersistent = true
    · have hvb' : st.viewBindI i = some (ty, b, mj) := by
        rw [EStore.viewBindI_pers hp, ← hpers, ← EStore.viewBindI_pers hp]; exact hvb
      have hch := h.bmChildOK i ty b mj hvb'
      exact ⟨by rw [hvbm mj]; exact hch.1, hch.2⟩
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [EStore.viewBindI_scr hp' hon', hscr, ← htb] at hvb
      rcases ETables.getBind_push_inv hvb with hold | ⟨h1, _, h3, _⟩
      · have hvb' : st.viewBindI i = some (ty, b, mj) := by
          rw [EStore.viewBindI_scr hp' hon]; exact hold
        have hch := h.bmChildOK i ty b mj hvb'
        exact ⟨by rw [hvbm mj]; exact hch.1, hch.2⟩
      · subst h3
        obtain ⟨m0, hm0⟩ := ENodeView.bmOf_of_isBind
          (by rw [← h1]; exact ETables.isBind_of_getBind hvb)
        refine ⟨by rw [hvbm mj, hmi m0 hm0]; rfl, ?_, hmi0⟩
        intro hpp; exact absurd (hpp.symm.trans hp') (by simp)
  case consP =>
    intro u i
    have hpf : st'.persFind? u = st.persFind? u := by
      simp only [EStore.persFind?, hfov, hpers]
    rw [hpf]
    constructor
    · intro hf
      obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
      exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact (h.consP u i).mpr ⟨by rwa [hviewP i h2] at h1, h2⟩
  case consS =>
    intro u i
    cases hmj : st.findBMOfView u with
    | none =>
      have hsf : st'.scrFind? u = none := by
        simp only [EStore.scrFind?, hfov, hmj]
      have hsfold : st.scrFind? u = none := by
        simp only [EStore.scrFind?, hmj]
      rw [hsf]
      refine ⟨fun hf => absurd hf (by simp), ?_⟩
      rintro ⟨h1, h2⟩
      exfalso
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · rw [(h.consS u i).mpr ⟨h3, h2⟩] at hsfold; exact absurd hsfold (by simp)
      · obtain ⟨mw, hw⟩ := hfovw; rw [hw] at hmj; exact absurd hmj (by simp)
    | some mj =>
      have hsf : st'.scrFind? u = tb.find? u mj := by
        simp only [EStore.scrFind?, hfov, hmj, hscr]
      have hsfold : st.scrFind? u = st.scr.find? u mj := by
        simp only [EStore.scrFind?, hmj]
      rw [hsf, hfindtb u mj hmj]
      constructor
      · intro hf
        by_cases hw : w = u
        · rw [if_pos hw] at hf
          have hii : inew = i := Option.some.inj hf
          subst hii; subst hw
          exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
        · rw [if_neg hw] at hf
          have hf' : st.scrFind? u = some i := by rw [hsfold]; exact hf
          obtain ⟨h1, h2⟩ := (h.consS u i).mp hf'
          exact ⟨hmono i u h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
        · have hf := (h.consS u i).mpr ⟨h3, h2⟩
          rw [hsfold] at hf
          have hw : w ≠ u := by
            rintro rfl
            rw [hprobe st.scr mj hmj, hfs] at hf
            exact absurd hf (by simp)
          rw [if_neg hw]; exact hf
        · rw [if_pos rfl]
  case fresh =>
    intro u i hf
    cases hmj : st.findBMOfView u with
    | none => simp only [EStore.persFind?, hfov, hmj]
    | some mj =>
      have hsf : st'.scrFind? u = tb.find? u mj := by
        simp only [EStore.scrFind?, hfov, hmj, hscr]
      rw [hsf, hfindtb u mj hmj] at hf
      have hpf : st'.persFind? u = st.pers.find? u mj := by
        simp only [EStore.persFind?, hfov, hmj, hpers]
      rw [hpf]
      by_cases hw : w = u
      · subst hw
        rw [hprobe st.pers mj hmj]
        exact hfp
      · rw [if_neg hw] at hf
        have hf' : st.scrFind? u = some i := by
          simp only [EStore.scrFind?, hmj]; exact hf
        have hfr := h.fresh u i hf'
        simp only [EStore.persFind?, hmj] at hfr
        exact hfr
  case bmConsP =>
    intro m j
    rw [hpers, hvbm j]
    exact h.bmConsP m j
  case bmConsS =>
    intro m j
    rw [hscr, ← htb, ETables.findBM_push, hvbm j]
    exact h.bmConsS m j
  case bmFresh =>
    intro m j hf
    rw [hscr, ← htb, ETables.findBM_push] at hf
    rw [hpers]
    exact h.bmFresh m j hf
  case bmKeyP =>
    intro u mj i hf
    rw [hpers] at hf ⊢
    exact h.bmKeyP u mj i hf
  case bmKeyS =>
    intro u mj i hf
    rw [hscr, ← htb, ETables.find?_push_gen] at hf
    cases hb : u.bmOf with
    | none => exact Or.inl rfl
    | some m0 =>
      by_cases hk : ETables.consKeyEq w mi u mj = true
      · obtain ⟨rfl, m', hm'⟩ := ETables.consKeyEq_bmOf hk hb
        exact Or.inr ⟨m', by rw [hfbm]; exact h.findBM_of_viewBM hmi0 (hmi m' hm')⟩
      · rw [if_neg hk] at hf
        rcases h.bmKeyS u mj i hf with h1 | ⟨m', h2⟩
        · rw [h1] at hb; exact absurd hb (by simp)
        · exact Or.inr ⟨m', by rw [hfbm]; exact h2⟩
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.expr, EStore.derived_scr hnp hon', hscr, hdernew]
  case bmDerExact =>
    intro j m hj
    rw [hvbm j] at hj
    have hbd : st'.bmDer j = st.bmDer j := by
      by_cases hjp : j.isPersistent = true
      · simp only [EStore.bmDer, EStore.persGetBMDer, hjp, if_true, hpers]
      · have hjp' : j.isPersistent = false := by simpa using hjp
        simp only [EStore.bmDer, EStore.persGetBMDer, hjp', hon, hon',
          Bool.false_eq_true, if_false, if_true, hscr, ← htb, ETables.getBMDer_push]
    rw [hbd]
    exact h.bmDerExact j m hj
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr]; exact hsizedtb
  case capP => rw [hpers]; exact h.capP
  case capS => rw [hscr]; exact hcaptb
  case bmCapP => rw [hpers]; exact h.bmCapP
  case bmCapS => rw [hscr, ← htb, ETables.bmSize_push]; exact h.bmCapS
  case scrOff => intro hoff; rw [hon'] at hoff; exact absurd hoff (by simp)

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
      reduceCtorEq, if_false, if_true] <;>
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
      beq_self_eq_true, if_true] <;>
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
      · rw [if_pos hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
      · rw [if_neg hw] at hf
        obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consS u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfs] at hf; exact absurd hf (by simp)
        rw [if_neg hw]; exact hf
      · rw [if_pos rfl]
  case fresh =>
    intro u i hf
    rw [hscr, hfindtb u] at hf
    rw [hpers]
    by_cases hw : w = u
    · subst hw; exact hfp
    · rw [if_neg hw] at hf; exact h.fresh u i hf
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
      · rw [if_pos hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [if_neg hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [if_neg hw]; exact hf
      · rw [if_pos rfl]
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
        rw [if_pos hon] at hcap
        exact NStore.wf_push_scr h hv hon hon rfl rfl rfl hcap hfp hfs
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [if_neg hoff] at hcap
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
      · rw [if_pos hon] at hcap
        have hspec := NTables.push_spec st.scr w (st.derOfView w) Idx.tierS
          (by decide) hcap
        have hp : ((st.scr.push w (st.derOfView w) Idx.tierS).2).isPersistent = false := by
          show (_ == 0) = false
          rw [hspec.2]; decide
        simp only [NStore.view]
        rw [if_neg (by simp [hp]), if_pos hon]
        exact hspec.1
    · rename_i hoff
      rw [if_neg hoff] at hcap
      have hspec := NTables.push_spec st.pers w (st.derOfView w) Idx.tierP
        (by decide) hcap
      have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [NStore.view]
      rw [if_pos hp]
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
        · rw [if_pos hp] at h ⊢; exact h
        · rw [if_neg hp] at h ⊢; exact NTables.get_push_mono _ _ _ _ h
    · rename_i hoff
      simp only [NStore.view, hoff] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [if_pos hp] at h ⊢; exact NTables.get_push_mono _ _ _ _ h
      · rw [if_neg hp] at h ⊢; exact h

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
    {mi : BMIdx} (hmi0 : mi.tag = 0) (hmi : ENodeView.BMOK st.viewBM w mi)
    (hpush : st.pers.push w (st.derOfView w) mi Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hfp : st.pers.find? w mi = none) :
    StoreWF st' ∧ st'.view inew = some w ∧ inew.isPersistent = true := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have hscrE : st.scr = ETables.empty := h.scrOff hon
  have htb : (st.pers.push w (st.derOfView w) mi Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.push w (st.derOfView w) mi Idx.tierP).2 = inew := by rw [hpush]
  -- the datum store is untouched, so `viewBM` and `findBM` do not move
  have hvbm : ∀ j : BMIdx, st'.viewBM j = st.viewBM j := by
    intro j
    by_cases hjp : j.isPersistent = true
    · rw [EStore.viewBM_pers hjp, EStore.viewBM_pers hjp, hpers, ← htb,
        ETables.getBM_push]
    · have hjp' : j.isPersistent = false := by simpa using hjp
      rw [EStore.viewBM_off hjp' hon', EStore.viewBM_off hjp' hon]
  have hfbm : ∀ m : ConLeche.BinderMeta, st'.findBM m = st.findBM m := by
    intro m
    simp only [EStore.findBM, EStore.persFindBM, hpers, hscr, hon, hon', ← htb,
      ETables.findBM_push]
  have hfov : ∀ v : ENodeView, st'.findBMOfView v = st.findBMOfView v := by
    intro v
    cases hb : v.bmOf with
    | none =>
      rw [EStore.findBMOfView_eq_zero _ hb, EStore.findBMOfView_eq_zero _ hb]
    | some m =>
      rw [EStore.findBMOfView_eq_findBM _ hb, EStore.findBMOfView_eq_findBM _ hb,
        hfbm]
  have hfovw : ∃ mw, st.findBMOfView w = some mw := by
    cases hb : w.bmOf with
    | none => exact ⟨_, EStore.findBMOfView_eq_zero _ hb⟩
    | some m =>
      exact ⟨mi, by rw [EStore.findBMOfView_eq_findBM _ hb,
        h.findBM_of_viewBM hmi0 (hmi m hb)]⟩
  have hprobe : ∀ (t : ETables) (mw : BMIdx), st.findBMOfView w = some mw →
      t.find? w mw = t.find? w mi := by
    intro t mw hw
    cases hb : w.bmOf with
    | none => exact ETables.find?_bmOf_none hb _ _
    | some m =>
      rw [EStore.findBMOfView_eq_findBM _ hb, h.findBM_of_viewBM hmi0 (hmi m hb)] at hw
      rw [Option.some.inj hw]
  -- the appended column, read back
  have hgetnew : tb.getWith st.viewBM inew = some w := by
    rw [← htb, ← hid]
    exact (ETables.getWith_push_spec st.pers st.viewBM w _ mi Idx.tierP hmi htr hcap).1
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid,
      (ETables.getWith_push_spec st.pers st.viewBM w _ mi Idx.tierP hmi htr hcap).2]
    decide
  have htag : inew.tag = w.tagOf := by rw [← hid]; exact ETables.push_tag htr hcap
  have hix : inew.idxNat = st.pers.sizeOf w := by
    rw [← hid]; exact ETables.push_idxNat htr hcap
  have hmonotb : ∀ i u, st.pers.getWith st.viewBM i = some u →
      tb.getWith st.viewBM i = some u := by
    intro i u hi; rw [← htb]; exact ETables.getWith_push_mono _ _ _ _ _ _ hi
  have hinvtb : ∀ i u, tb.getWith st.viewBM i = some u →
      st.pers.getWith st.viewBM i = some u ∨
        (i.tag = w.tagOf ∧ i.idxNat = st.pers.sizeOf w ∧ u = w) := by
    intro i u hi; rw [← htb] at hi; exact ETables.getWith_push_inv hmi hi
  have hfindtb : ∀ u mj, st.findBMOfView u = some mj →
      tb.find? u mj = if w = u then some inew else st.pers.find? u mj := by
    intro u mj hmj
    rw [← htb, ← hid, ETables.find?_push_gen]
    by_cases hk : ETables.consKeyEq w mi u mj = true
    · rw [if_pos hk, if_pos ((h.consKeyEq_iff hmi0 hmi hmj).mp hk)]
    · rw [if_neg hk, if_neg (fun he => hk ((h.consKeyEq_iff hmi0 hmi hmj).mpr he))]
  have hdertb : ∀ i, st.pers.Decodes i → tb.derAt i = st.pers.derAt i := by
    intro i hi; rw [← htb]; exact ETables.derAt_push_of_decodes h.sizedP hi
  have hdernew : tb.derAt inew = st.derOfView w := by
    rw [← htb, ← hid]; exact ETables.derAt_push_new h.sizedP htr hcap
  have hsizedtb : tb.Sized := by rw [← htb]; exact ETables.Sized_push h.sizedP
  have hcounttb : tb.count = st.pers.count + 1 := by rw [← htb]; exact ETables.count_push
  have hcaptb : ∀ u, tb.sizeOf u ≤ Idx.idxCap := by
    intro u
    rw [← htb]
    rcases ETables.sizeOf_push_cases (t := st.pers) (w := w) (v := u)
      (d := st.derOfView w) (mi := mi) (tr := Idx.tierP) with h1 | ⟨h1, _⟩
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
  have hviewP : ∀ i, i.isPersistent = true → st'.view i = tb.getWith st.viewBM i := by
    intro i hp
    rw [EStore.view_pers hp, hpers]
    exact ETables.getWith_congr (fun ty b mj _ => hvbm mj)
  have hviewPold : ∀ i, i.isPersistent = true →
      st.view i = st.pers.getWith st.viewBM i := fun i hp => EStore.view_pers hp
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
    rw [hviewPold inew hnp]; exact ETables.getWith_eq_none_of_size htag hix
  have hmono : ∀ i u, st.view i = some u → st'.view i = some u := by
    intro i u hu
    have hp := hallP i u hu
    rw [hviewP i hp]
    exact hmonotb i u (by rwa [hviewPold i hp] at hu)
  have hmoneS : ∀ i, (st.view i).isSome = true → (st'.view i).isSome = true := by
    intro i hi
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hi
    rw [hmono i u hu]; rfl
  have hinv : ∀ i u, st'.view i = some u → st.view i = some u ∨ (i = inew ∧ u = w) := by
    intro i u hu
    by_cases hp : i.isPersistent = true
    · rw [hviewP i hp] at hu
      rcases hinvtb i u hu with h1 | ⟨h2, h3, h4⟩
      · exact Or.inl (by rw [hviewPold i hp]; exact h1)
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
    exact hdertb i (ETables.Decodes_of_getWith (by rwa [hviewPold i hp] at hu))
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
      rankP := ?rankP, rankS := ?rankS, bmChildOK := ?bmChildOK,
      consP := ?consP, consS := ?consS, fresh := ?fresh,
      bmConsP := ?bmConsP, bmConsS := ?bmConsS, bmFresh := ?bmFresh,
      bmKeyP := ?bmKeyP, bmKeyS := ?bmKeyS,
      derExact := ?derExact, bmDerExact := ?bmDerExact, sizedP := ?sizedP,
      sizedS := ?sizedS, capP := ?capP, capS := ?capS, bmCapP := ?bmCapP,
      bmCapS := ?bmCapS, scrOff := ?scrOff,
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
  case bmChildOK =>
    intro i ty b mj hvb
    by_cases hp : i.isPersistent = true
    · rw [EStore.viewBindI_pers hp, hpers, ← htb] at hvb
      rcases ETables.getBind_push_inv hvb with hold | ⟨h1, _, h3, _⟩
      · have hvb' : st.viewBindI i = some (ty, b, mj) := by
          rw [EStore.viewBindI_pers hp]; exact hold
        have hch := h.bmChildOK i ty b mj hvb'
        exact ⟨by rw [hvbm mj]; exact hch.1, hch.2⟩
      · subst h3
        obtain ⟨m0, hm0⟩ := ENodeView.bmOf_of_isBind
          (by rw [← h1]; exact ETables.isBind_of_getBind hvb)
        have hbm0 : st.viewBM mj = some m0 := hmi m0 hm0
        have hmjP : mj.isPersistent = true := by
          by_cases hjp : mj.isPersistent = true
          · exact hjp
          · rw [EStore.viewBM_off (by simpa using hjp) hon] at hbm0
            exact absurd hbm0 (by simp)
        exact ⟨by rw [hvbm mj, hbm0]; rfl, fun _ => hmjP, hmi0⟩
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [EStore.viewBindI_off hp' hon'] at hvb
      exact absurd hvb (by simp)
  case consP =>
    intro u i
    cases hmj : st.findBMOfView u with
    | none =>
      have hpf : st'.persFind? u = none := by
        simp only [EStore.persFind?, hfov, hmj]
      have hpfold : st.persFind? u = none := by
        simp only [EStore.persFind?, hmj]
      rw [hpf]
      refine ⟨fun hf => absurd hf (by simp), ?_⟩
      rintro ⟨h1, h2⟩
      exfalso
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · rw [(h.consP u i).mpr ⟨h3, h2⟩] at hpfold; exact absurd hpfold (by simp)
      · obtain ⟨mw, hw⟩ := hfovw; rw [hw] at hmj; exact absurd hmj (by simp)
    | some mj =>
      have hpf : st'.persFind? u = tb.find? u mj := by
        simp only [EStore.persFind?, hfov, hmj, hpers]
      have hpfold : st.persFind? u = st.pers.find? u mj := by
        simp only [EStore.persFind?, hmj]
      rw [hpf, hfindtb u mj hmj]
      constructor
      · intro hf
        by_cases hw : w = u
        · rw [if_pos hw] at hf
          have hii : inew = i := Option.some.inj hf
          subst hii; subst hw
          exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
        · rw [if_neg hw] at hf
          have hf' : st.persFind? u = some i := by rw [hpfold]; exact hf
          obtain ⟨h1, h2⟩ := (h.consP u i).mp hf'
          exact ⟨hmono i u h1, h2⟩
      · rintro ⟨h1, h2⟩
        rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
        · have hf := (h.consP u i).mpr ⟨h3, h2⟩
          rw [hpfold] at hf
          have hw : w ≠ u := by
            rintro rfl
            rw [hprobe st.pers mj hmj, hfp] at hf
            exact absurd hf (by simp)
          rw [if_neg hw]; exact hf
        · rw [if_pos rfl]
  case consS =>
    intro u i
    have hsf : st'.scrFind? u = none := by
      simp only [EStore.scrFind?, hscr, hscrE]
      split
      · rfl
      · exact ETables.find?_empty u _
    rw [hsf]
    refine ⟨fun hf => absurd hf (by simp), ?_⟩
    rintro ⟨h1, h2⟩
    rw [hviewN' i h2] at h1; exact absurd h1 (by simp)
  case fresh =>
    intro u i hf
    have hsf : st'.scrFind? u = none := by
      simp only [EStore.scrFind?, hscr, hscrE]
      split
      · rfl
      · exact ETables.find?_empty u _
    rw [hsf] at hf; exact absurd hf (by simp)
  case bmConsP =>
    intro m j
    rw [hpers, ← htb, ETables.findBM_push, hvbm j]
    exact h.bmConsP m j
  case bmConsS =>
    intro m j
    rw [hscr, hvbm j]
    exact h.bmConsS m j
  case bmFresh =>
    intro m j hf
    rw [hscr] at hf
    rw [hpers, ← htb, ETables.findBM_push]
    exact h.bmFresh m j hf
  case bmKeyP =>
    intro u mj i hf
    have hfbmP : ∀ m : ConLeche.BinderMeta, st.findBM m = st.pers.findBM m := by
      intro m
      simp only [EStore.findBM, EStore.persFindBM, hon, Bool.false_eq_true, if_false]
      cases st.pers.findBM m <;> rfl
    have hpfbm : ∀ m : ConLeche.BinderMeta, st'.pers.findBM m = st.pers.findBM m := by
      intro m; rw [hpers, ← htb, ETables.findBM_push]
    rw [hpers, ← htb, ETables.find?_push_gen] at hf
    cases hb : u.bmOf with
    | none => exact Or.inl rfl
    | some m0 =>
      by_cases hk : ETables.consKeyEq w mi u mj = true
      · obtain ⟨rfl, m', hm'⟩ := ETables.consKeyEq_bmOf hk hb
        refine Or.inr ⟨m', ?_⟩
        rw [hpfbm, ← hfbmP]
        exact h.findBM_of_viewBM hmi0 (hmi m' hm')
      · rw [if_neg hk] at hf
        rcases h.bmKeyP u mj i hf with h1 | ⟨m', h2⟩
        · rw [h1] at hb; exact absurd hb (by simp)
        · exact Or.inr ⟨m', by rw [hpfbm]; exact h2⟩
  case bmKeyS =>
    intro u mj i hf
    rw [hscr, hscrE, ETables.find?_empty] at hf; exact absurd hf (by simp)
  case derExact =>
    intro i u hi
    rcases hinv i u hi with hi' | ⟨rfl, rfl⟩
    · rw [hdov u (fun c hc => (h.childOK i u hi' c hc).1), hder i (by rw [hi']; rfl)]
      exact h.derExact i u hi'
    · rw [hdov u hv.expr, EStore.derived_pers hnp, hpers, hdernew]
  case bmDerExact =>
    intro j m hj
    rw [hvbm j] at hj
    have hbd : st'.bmDer j = st.bmDer j := by
      by_cases hjp : j.isPersistent = true
      · simp only [EStore.bmDer, EStore.persGetBMDer, hjp, if_true, hpers, ← htb,
          ETables.getBMDer_push]
      · have hjp' : j.isPersistent = false := by simpa using hjp
        simp only [EStore.bmDer, EStore.persGetBMDer, hjp', hon, hon',
          Bool.false_eq_true, if_false]
    rw [hbd]
    exact h.bmDerExact j m hj
  case sizedP => rw [hpers]; exact hsizedtb
  case sizedS => rw [hscr]; exact h.sizedS
  case capP => rw [hpers]; exact hcaptb
  case capS => rw [hscr]; exact h.capS
  case bmCapP => rw [hpers, ← htb, ETables.bmSize_push]; exact h.bmCapP
  case bmCapS => rw [hscr]; exact h.bmCapS
  case scrOff => intro _; rw [hscr]; exact hscrE

/-! ### The binder datum's own append

`internBM` is `intern`'s clauses at a store with ONE constructor and no
children, and the two lemmas below are its `wf_push_scr` / `wf_push_pers`.
The datum push leaves every node read, `find?`, `derAt` and `count` of the
tier untouched, so `view` does not move at all — `bmChildOK` says the data a
node names already decode, and `getBM` only grows.  What moves are the seven
`bm*` clauses and the cons probes of the ONE view whose datum has just become
findable: before the push `findBMOfView` answered `none` there, so `consP` and
`consS` said nothing about that view, and after it they must say that the
fresh handle finds nothing — which is exactly what `bmKeyP`/`bmKeyS` deliver
(task #97-LC §6, finding 3). -/

/-- con-leche: none — arena infrastructure; appending a binder DATUM to the
scratch tier keeps the store invariant. -/
theorem EStore.wf_pushBM_scr {st st' : EStore} {rk : EIdx → Nat}
    {m : ConLeche.BinderMeta} {tb : ETables} {inew : BMIdx}
    (h : EWFAt st rk)
    (hon : st.scratchOn = true) (hon' : st'.scratchOn = true)
    (hlss : st'.lss = st.lss) (hpers : st'.pers = st.pers)
    (hpush : st.scr.pushBM m (hash m.pw) Idx.tierS = (tb, inew))
    (hscr : st'.scr = tb)
    (hcap : st.scr.bms.size < Idx.idxCap)
    (hfp : st.pers.findBM m = none) (hfs : st.scr.findBM m = none) :
    EWFAt st' rk ∧ (∀ i : EIdx, st'.view i = st.view i) ∧
      st'.viewBM inew = some m ∧ inew.tag = 0 := by
  have htr : (Idx.tierS : UInt32).toNat < 2 := by decide
  have htb : (st.scr.pushBM m (hash m.pw) Idx.tierS).1 = tb := by rw [hpush]
  have hid : (st.scr.pushBM m (hash m.pw) Idx.tierS).2 = inew := by rw [hpush]
  have hpweq : ∀ mm : ConLeche.BinderMeta, m.pw = mm.pw → mm = m := by
    intro mm hmm; cases m; cases mm; simp_all
  -- the appended handle
  have hnp : inew.isPersistent = false := by
    show (inew.tier == 0) = false
    rw [← hid, ETables.pushBM_tier htr hcap]; decide
  have htag0 : inew.tag = 0 := by rw [← hid]; exact ETables.pushBM_tag htr hcap
  have hix : inew.idxNat = st.scr.bms.size := by
    rw [← hid]; exact ETables.pushBM_idxNat htr hcap
  have hinewNone : st.viewBM inew = none := by
    rw [EStore.viewBM_scr hnp hon]
    simp [ETables.getBM, hix, Tbl.node?_size]
  -- the datum store, before and after
  have hbmMono : ∀ (j : BMIdx) (mm : ConLeche.BinderMeta),
      st.viewBM j = some mm → st'.viewBM j = some mm := by
    intro j mm hj
    by_cases hjp : j.isPersistent = true
    · rw [EStore.viewBM_pers hjp, hpers]; rw [EStore.viewBM_pers hjp] at hj; exact hj
    · have hjp' : j.isPersistent = false := by simpa using hjp
      rw [EStore.viewBM_scr hjp' hon', hscr, ← htb]
      rw [EStore.viewBM_scr hjp' hon] at hj
      exact ETables.getBM_pushBM_mono hj
  have hbmInv : ∀ (j : BMIdx) (mm : ConLeche.BinderMeta), st'.viewBM j = some mm →
      st.viewBM j = some mm ∨
        (j.idxNat = st.scr.bms.size ∧ j.isPersistent = false ∧ mm = m) := by
    intro j mm hj
    by_cases hjp : j.isPersistent = true
    · rw [EStore.viewBM_pers hjp, hpers] at hj
      exact Or.inl (by rw [EStore.viewBM_pers hjp]; exact hj)
    · have hjp' : j.isPersistent = false := by simpa using hjp
      rw [EStore.viewBM_scr hjp' hon', hscr, ← htb] at hj
      rcases ETables.getBM_pushBM_inv hj with h1 | ⟨h1, h2⟩
      · exact Or.inl (by rw [EStore.viewBM_scr hjp' hon]; exact h1)
      · exact Or.inr ⟨h1, hjp', h2⟩
  have hbmNew : st'.viewBM inew = some m := by
    rw [EStore.viewBM_scr hnp hon', hscr, ← htb]
    exact ETables.getBM_pushBM_at_size hix
  have hbmEq : ∀ j : BMIdx, (st.viewBM j).isSome = true →
      st'.viewBM j = st.viewBM j := by
    intro j hj
    obtain ⟨mm, hmm⟩ := Option.isSome_iff_exists.mp hj
    rw [hmm]; exact hbmMono j mm hmm
  -- the datum's cons probe
  have hfindBMold : st.findBM m = none := by
    simp only [EStore.findBM, EStore.persFindBM, hfp, hon, if_true, hfs]
  have hfbmNew : st'.findBM m = some inew := by
    have h1 : st'.pers.findBM m = none := by rw [hpers]; exact hfp
    have h2 : st'.scr.findBM m = some inew := by
      rw [hscr, ← htb, ETables.findBM_pushBM, if_pos rfl, hid]
    simp only [EStore.findBM, EStore.persFindBM, h1, hon', if_true, h2]
  have hfbmEq : ∀ mm : ConLeche.BinderMeta, ¬ (m.pw = mm.pw) →
      st'.findBM mm = st.findBM mm := by
    intro mm hk
    simp only [EStore.findBM, EStore.persFindBM, hpers, hon, hon', hscr, ← htb,
      ETables.findBM_pushBM, if_neg hk]
  have hfindBMmono : ∀ (mm : ConLeche.BinderMeta) (j : BMIdx),
      st.findBM mm = some j → st'.findBM mm = some j := by
    intro mm j hj
    by_cases hk : m.pw = mm.pw
    · have hmm : mm = m := hpweq mm hk
      subst hmm; rw [hfindBMold] at hj; exact absurd hj (by simp)
    · rw [hfbmEq mm hk]; exact hj
  -- the node side does not move
  have hviewBindI : ∀ i : EIdx, st'.viewBindI i = st.viewBindI i := by
    intro i
    by_cases hp : i.isPersistent = true
    · rw [EStore.viewBindI_pers hp, EStore.viewBindI_pers hp, hpers]
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [EStore.viewBindI_scr hp' hon', EStore.viewBindI_scr hp' hon, hscr, ← htb,
        ETables.getBind_pushBM]
  have hview : ∀ i : EIdx, st'.view i = st.view i := by
    intro i
    by_cases hp : i.isPersistent = true
    · rw [EStore.view_pers hp, EStore.view_pers hp, hpers]
      refine ETables.getWith_congr ?_
      intro ty b mj hg
      exact hbmEq mj
        (h.bmChildOK i ty b mj (by rw [EStore.viewBindI_pers hp]; exact hg)).1
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [EStore.view_scr hp' hon', EStore.view_scr hp' hon, hscr, ← htb,
        ETables.getWith_pushBM]
      refine ETables.getWith_congr ?_
      intro ty b mj hg
      exact hbmEq mj
        (h.bmChildOK i ty b mj (by rw [EStore.viewBindI_scr hp' hon]; exact hg)).1
  have hder : ∀ i : EIdx, st'.derived i = st.derived i := by
    intro i
    by_cases hp : i.isPersistent = true
    · rw [EStore.derived_pers hp, EStore.derived_pers hp, hpers]
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [EStore.derived_scr hp' hon', EStore.derived_scr hp' hon, hscr, ← htb,
        ETables.derAt_pushBM]
  have hns : st'.ns = st.ns := by simp only [EStore.ns, hlss]
  have hls : st'.ls = st.ls := by simp only [EStore.ls, hlss]
  have hdov : ∀ u : ENodeView, st'.derOfView u = st.derOfView u := by
    intro u
    refine EStore.derOfView_congr (fun c _ => hder c) ?_ ?_ ?_ <;>
      intro c _ <;>
      simp only [EStore.nder, EStore.lder, EStore.lsder, hns, hls, hlss]
  have hpc : st'.persCount = st.persCount := by simp only [EStore.persCount, hpers]
  have hnc : st'.nodeCount = st.nodeCount := by
    simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, hpers, hscr,
      ← htb, ETables.count_pushBM]
  -- the view whose datum the push has just made findable
  have hnoView : ∀ (u : ENodeView) (i : EIdx), u.bmOf = some m →
      st'.view i = some u → False := by
    intro u i hb hi
    rw [hview i] at hi
    obtain ⟨mj, hmj⟩ := h.findBM_of_view hi hb
    rw [hfindBMold] at hmj; exact absurd hmj (by simp)
  have hpfNew : ∀ u : ENodeView, u.bmOf = some m → st'.persFind? u = none := by
    intro u hb
    have hfv : st'.findBMOfView u = some inew := by
      rw [EStore.findBMOfView_eq_findBM _ hb]; exact hfbmNew
    simp only [EStore.persFind?, hfv, hpers]
    cases hc : st.pers.find? u inew with
    | none => rfl
    | some i0 =>
      exfalso
      rcases h.bmKeyP u inew i0 hc with h1 | ⟨m', h2⟩
      · rw [h1] at hb; exact absurd hb (by simp)
      · have hvv := ((h.bmConsP m' inew).mp h2).1
        rw [hinewNone] at hvv; exact absurd hvv (by simp)
  have hsfNew : ∀ u : ENodeView, u.bmOf = some m → st'.scrFind? u = none := by
    intro u hb
    have hfv : st'.findBMOfView u = some inew := by
      rw [EStore.findBMOfView_eq_findBM _ hb]; exact hfbmNew
    simp only [EStore.scrFind?, hfv, hscr, ← htb, ETables.find?_pushBM]
    cases hc : st.scr.find? u inew with
    | none => rfl
    | some i0 =>
      exfalso
      rcases h.bmKeyS u inew i0 hc with h1 | ⟨m', h2⟩
      · rw [h1] at hb; exact absurd hb (by simp)
      · have hvv := h.viewBM_of_findBM h2
        rw [hinewNone] at hvv; exact absurd hvv (by simp)
  -- every other view's probes are the old ones
  have hfovEq : ∀ u : ENodeView, (∀ mm, u.bmOf = some mm → mm ≠ m) →
      st'.findBMOfView u = st.findBMOfView u := by
    intro u hne
    cases hb : u.bmOf with
    | none => rw [EStore.findBMOfView_eq_zero _ hb, EStore.findBMOfView_eq_zero _ hb]
    | some mm =>
      rw [EStore.findBMOfView_eq_findBM _ hb, EStore.findBMOfView_eq_findBM _ hb]
      exact hfbmEq mm (fun hk => hne mm hb (hpweq mm hk))
  have hpfEq : ∀ u : ENodeView, (∀ mm, u.bmOf = some mm → mm ≠ m) →
      st'.persFind? u = st.persFind? u := by
    intro u hne
    simp only [EStore.persFind?, hfovEq u hne, hpers]
  have hsfEq : ∀ u : ENodeView, (∀ mm, u.bmOf = some mm → mm ≠ m) →
      st'.scrFind? u = st.scrFind? u := by
    intro u hne
    simp only [EStore.scrFind?, hfovEq u hne, hscr, ← htb, ETables.find?_pushBM]
  refine ⟨?wf, hview, hbmNew, htag0⟩
  case wf =>
  refine { lss := by rw [hlss]; exact h.lss, childOK := ?childOK,
           nchildOK := ?nchildOK, lchildOK := ?lchildOK, lschildOK := ?lschildOK,
           rankP := ?rankP, rankS := ?rankS, bmChildOK := ?bmChildOK,
           consP := ?consP, consS := ?consS, fresh := ?fresh,
           bmConsP := ?bmConsP, bmConsS := ?bmConsS, bmFresh := ?bmFresh,
           bmKeyP := ?bmKeyP, bmKeyS := ?bmKeyS,
           derExact := ?derExact, bmDerExact := ?bmDerExact,
           sizedP := ?sizedP, sizedS := ?sizedS, capP := ?capP, capS := ?capS,
           bmCapP := ?bmCapP, bmCapS := ?bmCapS, scrOff := ?scrOff,
           sync := by rw [hon', hlss, ← h.sync, hon] }
  case childOK =>
    intro i u hi c hc
    rw [hview i] at hi
    have hch := h.childOK i u hi c hc
    exact ⟨by rw [hview c]; exact hch.1, hch.2.1, hch.2.2⟩
  case nchildOK =>
    intro i u hi c hc
    rw [hview i] at hi; rw [hns]; exact h.nchildOK i u hi c hc
  case lchildOK =>
    intro i u hi c hc
    rw [hview i] at hi; rw [hls]; exact h.lchildOK i u hi c hc
  case lschildOK =>
    intro i u hi c hc
    rw [hview i] at hi; rw [hlss]; exact h.lschildOK i u hi c hc
  case rankP =>
    intro i hp hi
    rw [hview i] at hi; rw [hpc]; exact h.rankP i hp hi
  case rankS =>
    intro i hp hi
    rw [hview i] at hi; rw [hnc]; exact h.rankS i hp hi
  case bmChildOK =>
    intro i ty b mj hvb
    rw [hviewBindI i] at hvb
    have hch := h.bmChildOK i ty b mj hvb
    exact ⟨by rw [hbmEq mj hch.1]; exact hch.1, hch.2.1, hch.2.2⟩
  case consP =>
    intro u i
    by_cases hb : u.bmOf = some m
    · rw [hpfNew u hb]
      exact ⟨fun hf => absurd hf (by simp), fun hx => (hnoView u i hb hx.1).elim⟩
    · have hne : ∀ mm, u.bmOf = some mm → mm ≠ m := by
        intro mm hmm hmm2; exact hb (hmm2 ▸ hmm)
      rw [hpfEq u hne, hview i]; exact h.consP u i
  case consS =>
    intro u i
    by_cases hb : u.bmOf = some m
    · rw [hsfNew u hb]
      exact ⟨fun hf => absurd hf (by simp), fun hx => (hnoView u i hb hx.1).elim⟩
    · have hne : ∀ mm, u.bmOf = some mm → mm ≠ m := by
        intro mm hmm hmm2; exact hb (hmm2 ▸ hmm)
      rw [hsfEq u hne, hview i]; exact h.consS u i
  case fresh =>
    intro u i hf
    by_cases hb : u.bmOf = some m
    · rw [hsfNew u hb] at hf; exact absurd hf (by simp)
    · have hne : ∀ mm, u.bmOf = some mm → mm ≠ m := by
        intro mm hmm hmm2; exact hb (hmm2 ▸ hmm)
      rw [hsfEq u hne] at hf; rw [hpfEq u hne]; exact h.fresh u i hf
  case bmConsP =>
    intro mm j
    rw [hpers]
    constructor
    · intro hf
      obtain ⟨h1, h2, h3⟩ := (h.bmConsP mm j).mp hf
      exact ⟨hbmMono j mm h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      rcases hbmInv j mm h1 with hh | ⟨_, hjp, _⟩
      · exact (h.bmConsP mm j).mpr ⟨hh, h2, h3⟩
      · rw [hjp] at h2; exact absurd h2 (by simp)
  case bmConsS =>
    intro mm j
    rw [hscr, ← htb, ETables.findBM_pushBM]
    constructor
    · intro hf
      by_cases hk : m.pw = mm.pw
      · rw [if_pos hk, hid] at hf
        have hji : inew = j := Option.some.inj hf
        subst hji
        have hmm : mm = m := hpweq mm hk
        subst hmm
        exact ⟨hbmNew, hnp, htag0⟩
      · rw [if_neg hk] at hf
        obtain ⟨h1, h2, h3⟩ := (h.bmConsS mm j).mp hf
        exact ⟨hbmMono j mm h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      rcases hbmInv j mm h1 with hh | ⟨hix2, _, hmm3⟩
      · have hne : ¬ (m.pw = mm.pw) := by
          intro hk
          have hmm : mm = m := hpweq mm hk
          subst hmm
          rw [(h.bmConsS mm j).mpr ⟨hh, h2, h3⟩] at hfs; exact absurd hfs (by simp)
        rw [if_neg hne]
        exact (h.bmConsS mm j).mpr ⟨hh, h2, h3⟩
      · subst hmm3
        rw [if_pos rfl, hid]
        exact congrArg some (Idx.eq_of_idxNat (htag0.trans h3.symm)
          ((Idx.tier_eq_tierS hnp).trans (Idx.tier_eq_tierS h2).symm)
          (hix.trans hix2.symm))
  case bmFresh =>
    intro mm j hf
    rw [hscr, ← htb, ETables.findBM_pushBM] at hf
    rw [hpers]
    by_cases hk : m.pw = mm.pw
    · have hmm : mm = m := hpweq mm hk
      subst hmm; exact hfp
    · rw [if_neg hk] at hf; exact h.bmFresh mm j hf
  case bmKeyP =>
    intro u mj i hf
    rw [hpers] at hf ⊢
    exact h.bmKeyP u mj i hf
  case bmKeyS =>
    intro u mj i hf
    rw [hscr, ← htb, ETables.find?_pushBM] at hf
    rcases h.bmKeyS u mj i hf with h1 | ⟨m', h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨m', hfindBMmono m' mj h2⟩
  case derExact =>
    intro i u hi
    rw [hview i] at hi
    rw [hdov u, hder i]
    exact h.derExact i u hi
  case bmDerExact =>
    intro j mm hj
    rcases hbmInv j mm hj with hh | ⟨hix2, hjp0, hmm3⟩
    · have hbd : st'.bmDer j = st.bmDer j := by
        by_cases hjp : j.isPersistent = true
        · simp only [EStore.bmDer, EStore.persGetBMDer, hjp, if_true, hpers]
        · have hjp' : j.isPersistent = false := by simpa using hjp
          have hlt : j.idxNat < st.scr.bms.size := by
            rw [EStore.viewBM_scr hjp' hon] at hh
            simp only [ETables.getBM] at hh
            exact Tbl.lt_of_map hh
          simp only [EStore.bmDer, EStore.persGetBMDer, hjp', hon, hon',
            Bool.false_eq_true, if_false, if_true, hscr, ← htb,
            ETables.getBMDer_pushBM_of_lt (ETables.bms_Sized h.sizedS) hlt]
      rw [hbd]; exact h.bmDerExact j mm hh
    · subst hmm3
      simp only [EStore.bmDer, EStore.persGetBMDer, hjp0, hon', Bool.false_eq_true,
        if_false, if_true, hscr, ← htb,
        ETables.getBMDer_pushBM_at_size (ETables.bms_Sized h.sizedS) hix2]
  case sizedP => rw [hpers]; exact h.sizedP
  case sizedS => rw [hscr, ← htb]; exact ETables.Sized_pushBM h.sizedS
  case capP => rw [hpers]; exact h.capP
  case capS =>
    intro u; rw [hscr, ← htb, ETables.sizeOf_pushBM]; exact h.capS u
  case bmCapP => rw [hpers]; exact h.bmCapP
  case bmCapS =>
    rw [hscr, ← htb, ETables.bmSize_pushBM, ETables.bmSize_eq]
    omega
  case scrOff => intro hoff; rw [hon'] at hoff; exact absurd hoff (by simp)

/-- con-leche: none — arena infrastructure; appending a binder DATUM to the
persistent tier keeps the store invariant.  The scratch tier is empty here
(`scrOff`), which is what makes the datum's `fresh` clauses free. -/
theorem EStore.wf_pushBM_pers {st st' : EStore} {rk : EIdx → Nat}
    {m : ConLeche.BinderMeta} {tb : ETables} {inew : BMIdx}
    (h : EWFAt st rk)
    (hon : st.scratchOn = false) (hon' : st'.scratchOn = false)
    (hlss : st'.lss = st.lss) (hscr : st'.scr = st.scr)
    (hpush : st.pers.pushBM m (hash m.pw) Idx.tierP = (tb, inew))
    (hpers : st'.pers = tb)
    (hcap : st.pers.bms.size < Idx.idxCap)
    (hfp : st.pers.findBM m = none) :
    EWFAt st' rk ∧ (∀ i : EIdx, st'.view i = st.view i) ∧
      st'.viewBM inew = some m ∧ inew.tag = 0 := by
  have htr : (Idx.tierP : UInt32).toNat < 2 := by decide
  have hscrE : st.scr = ETables.empty := h.scrOff hon
  have htb : (st.pers.pushBM m (hash m.pw) Idx.tierP).1 = tb := by rw [hpush]
  have hid : (st.pers.pushBM m (hash m.pw) Idx.tierP).2 = inew := by rw [hpush]
  have hpweq : ∀ mm : ConLeche.BinderMeta, m.pw = mm.pw → mm = m := by
    intro mm hmm; cases m; cases mm; simp_all
  -- the appended handle
  have hnp : inew.isPersistent = true := by
    show (inew.tier == 0) = true
    rw [← hid, ETables.pushBM_tier htr hcap]; decide
  have htag0 : inew.tag = 0 := by rw [← hid]; exact ETables.pushBM_tag htr hcap
  have hix : inew.idxNat = st.pers.bms.size := by
    rw [← hid]; exact ETables.pushBM_idxNat htr hcap
  have hinewNone : st.viewBM inew = none := by
    rw [EStore.viewBM_pers hnp]
    simp [ETables.getBM, hix, Tbl.node?_size]
  -- the datum store, before and after
  have hbmMono : ∀ (j : BMIdx) (mm : ConLeche.BinderMeta),
      st.viewBM j = some mm → st'.viewBM j = some mm := by
    intro j mm hj
    by_cases hjp : j.isPersistent = true
    · rw [EStore.viewBM_pers hjp, hpers, ← htb]
      rw [EStore.viewBM_pers hjp] at hj
      exact ETables.getBM_pushBM_mono hj
    · have hjp' : j.isPersistent = false := by simpa using hjp
      rw [EStore.viewBM_off hjp' hon] at hj; exact absurd hj (by simp)
  have hbmInv : ∀ (j : BMIdx) (mm : ConLeche.BinderMeta), st'.viewBM j = some mm →
      st.viewBM j = some mm ∨
        (j.idxNat = st.pers.bms.size ∧ j.isPersistent = true ∧ mm = m) := by
    intro j mm hj
    by_cases hjp : j.isPersistent = true
    · rw [EStore.viewBM_pers hjp, hpers, ← htb] at hj
      rcases ETables.getBM_pushBM_inv hj with h1 | ⟨h1, h2⟩
      · exact Or.inl (by rw [EStore.viewBM_pers hjp]; exact h1)
      · exact Or.inr ⟨h1, hjp, h2⟩
    · have hjp' : j.isPersistent = false := by simpa using hjp
      rw [EStore.viewBM_off hjp' hon'] at hj; exact absurd hj (by simp)
  have hbmNew : st'.viewBM inew = some m := by
    rw [EStore.viewBM_pers hnp, hpers, ← htb]
    exact ETables.getBM_pushBM_at_size hix
  have hbmEq : ∀ j : BMIdx, (st.viewBM j).isSome = true →
      st'.viewBM j = st.viewBM j := by
    intro j hj
    obtain ⟨mm, hmm⟩ := Option.isSome_iff_exists.mp hj
    rw [hmm]; exact hbmMono j mm hmm
  -- the datum's cons probe
  have hfindBMold : st.findBM m = none := by
    simp only [EStore.findBM, EStore.persFindBM, hfp, hon, Bool.false_eq_true, if_false]
  have hfbmNew : st'.findBM m = some inew := by
    have h1 : st'.pers.findBM m = some inew := by
      rw [hpers, ← htb, ETables.findBM_pushBM, if_pos rfl, hid]
    simp only [EStore.findBM, EStore.persFindBM, h1]
  have hpfbmEq : ∀ mm : ConLeche.BinderMeta, ¬ (m.pw = mm.pw) →
      st'.pers.findBM mm = st.pers.findBM mm := by
    intro mm hk
    rw [hpers, ← htb, ETables.findBM_pushBM, if_neg hk]
  have hfbmEq : ∀ mm : ConLeche.BinderMeta, ¬ (m.pw = mm.pw) →
      st'.findBM mm = st.findBM mm := by
    intro mm hk
    simp only [EStore.findBM, EStore.persFindBM, hpfbmEq mm hk, hon, hon',
      Bool.false_eq_true, if_false]
  have hfindBMmono : ∀ (mm : ConLeche.BinderMeta) (j : BMIdx),
      st.findBM mm = some j → st'.findBM mm = some j := by
    intro mm j hj
    by_cases hk : m.pw = mm.pw
    · have hmm : mm = m := hpweq mm hk
      subst hmm; rw [hfindBMold] at hj; exact absurd hj (by simp)
    · rw [hfbmEq mm hk]; exact hj
  have hpersFindBMmono : ∀ (mm : ConLeche.BinderMeta) (j : BMIdx),
      st.pers.findBM mm = some j → st'.pers.findBM mm = some j := by
    intro mm j hj
    by_cases hk : m.pw = mm.pw
    · have hmm : mm = m := hpweq mm hk
      subst hmm; rw [hfp] at hj; exact absurd hj (by simp)
    · rw [hpfbmEq mm hk]; exact hj
  -- the node side does not move
  have hviewBindI : ∀ i : EIdx, st'.viewBindI i = st.viewBindI i := by
    intro i
    by_cases hp : i.isPersistent = true
    · rw [EStore.viewBindI_pers hp, EStore.viewBindI_pers hp, hpers, ← htb,
        ETables.getBind_pushBM]
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [EStore.viewBindI_off hp' hon', EStore.viewBindI_off hp' hon]
  have hview : ∀ i : EIdx, st'.view i = st.view i := by
    intro i
    by_cases hp : i.isPersistent = true
    · rw [EStore.view_pers hp, EStore.view_pers hp, hpers, ← htb,
        ETables.getWith_pushBM]
      refine ETables.getWith_congr ?_
      intro ty b mj hg
      exact hbmEq mj
        (h.bmChildOK i ty b mj (by rw [EStore.viewBindI_pers hp]; exact hg)).1
    · have hp' : i.isPersistent = false := by simpa using hp
      rw [EStore.view_off hp' hon', EStore.view_off hp' hon]
  have hder : ∀ i : EIdx, st'.derived i = st.derived i := by
    intro i
    by_cases hp : i.isPersistent = true
    · rw [EStore.derived_pers hp, EStore.derived_pers hp, hpers, ← htb,
        ETables.derAt_pushBM]
    · have hp' : i.isPersistent = false := by simpa using hp
      simp only [EStore.derived, hp', hon, hon', Bool.false_eq_true, if_false]
  have hns : st'.ns = st.ns := by simp only [EStore.ns, hlss]
  have hls : st'.ls = st.ls := by simp only [EStore.ls, hlss]
  have hdov : ∀ u : ENodeView, st'.derOfView u = st.derOfView u := by
    intro u
    refine EStore.derOfView_congr (fun c _ => hder c) ?_ ?_ ?_ <;>
      intro c _ <;>
      simp only [EStore.nder, EStore.lder, EStore.lsder, hns, hls, hlss]
  have hpc : st'.persCount = st.persCount := by
    simp only [EStore.persCount, hpers, ← htb, ETables.count_pushBM]
  have hnc : st'.nodeCount = st.nodeCount := by
    simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount, hpers, hscr,
      ← htb, ETables.count_pushBM]
  -- the view whose datum the push has just made findable
  have hnoView : ∀ (u : ENodeView) (i : EIdx), u.bmOf = some m →
      st'.view i = some u → False := by
    intro u i hb hi
    rw [hview i] at hi
    obtain ⟨mj, hmj⟩ := h.findBM_of_view hi hb
    rw [hfindBMold] at hmj; exact absurd hmj (by simp)
  have hpfNew : ∀ u : ENodeView, u.bmOf = some m → st'.persFind? u = none := by
    intro u hb
    have hfv : st'.findBMOfView u = some inew := by
      rw [EStore.findBMOfView_eq_findBM _ hb]; exact hfbmNew
    simp only [EStore.persFind?, hfv, hpers, ← htb, ETables.find?_pushBM]
    cases hc : st.pers.find? u inew with
    | none => rfl
    | some i0 =>
      exfalso
      rcases h.bmKeyP u inew i0 hc with h1 | ⟨m', h2⟩
      · rw [h1] at hb; exact absurd hb (by simp)
      · have hvv := ((h.bmConsP m' inew).mp h2).1
        rw [hinewNone] at hvv; exact absurd hvv (by simp)
  have hsfNew : ∀ u : ENodeView, u.bmOf = some m → st'.scrFind? u = none := by
    intro u hb
    have hfv : st'.findBMOfView u = some inew := by
      rw [EStore.findBMOfView_eq_findBM _ hb]; exact hfbmNew
    simp only [EStore.scrFind?, hfv, hscr, hscrE]
    exact ETables.find?_empty u _
  -- every other view's probes are the old ones
  have hfovEq : ∀ u : ENodeView, (∀ mm, u.bmOf = some mm → mm ≠ m) →
      st'.findBMOfView u = st.findBMOfView u := by
    intro u hne
    cases hb : u.bmOf with
    | none => rw [EStore.findBMOfView_eq_zero _ hb, EStore.findBMOfView_eq_zero _ hb]
    | some mm =>
      rw [EStore.findBMOfView_eq_findBM _ hb, EStore.findBMOfView_eq_findBM _ hb]
      exact hfbmEq mm (fun hk => hne mm hb (hpweq mm hk))
  have hpfEq : ∀ u : ENodeView, (∀ mm, u.bmOf = some mm → mm ≠ m) →
      st'.persFind? u = st.persFind? u := by
    intro u hne
    simp only [EStore.persFind?, hfovEq u hne, hpers, ← htb, ETables.find?_pushBM]
  have hsfEq : ∀ u : ENodeView, (∀ mm, u.bmOf = some mm → mm ≠ m) →
      st'.scrFind? u = st.scrFind? u := by
    intro u hne
    simp only [EStore.scrFind?, hfovEq u hne, hscr]
  refine ⟨?wf, hview, hbmNew, htag0⟩
  case wf =>
  refine { lss := by rw [hlss]; exact h.lss, childOK := ?childOK,
           nchildOK := ?nchildOK, lchildOK := ?lchildOK, lschildOK := ?lschildOK,
           rankP := ?rankP, rankS := ?rankS, bmChildOK := ?bmChildOK,
           consP := ?consP, consS := ?consS, fresh := ?fresh,
           bmConsP := ?bmConsP, bmConsS := ?bmConsS, bmFresh := ?bmFresh,
           bmKeyP := ?bmKeyP, bmKeyS := ?bmKeyS,
           derExact := ?derExact, bmDerExact := ?bmDerExact,
           sizedP := ?sizedP, sizedS := ?sizedS, capP := ?capP, capS := ?capS,
           bmCapP := ?bmCapP, bmCapS := ?bmCapS, scrOff := ?scrOff,
           sync := by rw [hon', hlss, ← h.sync, hon] }
  case childOK =>
    intro i u hi c hc
    rw [hview i] at hi
    have hch := h.childOK i u hi c hc
    exact ⟨by rw [hview c]; exact hch.1, hch.2.1, hch.2.2⟩
  case nchildOK =>
    intro i u hi c hc
    rw [hview i] at hi; rw [hns]; exact h.nchildOK i u hi c hc
  case lchildOK =>
    intro i u hi c hc
    rw [hview i] at hi; rw [hls]; exact h.lchildOK i u hi c hc
  case lschildOK =>
    intro i u hi c hc
    rw [hview i] at hi; rw [hlss]; exact h.lschildOK i u hi c hc
  case rankP =>
    intro i hp hi
    rw [hview i] at hi; rw [hpc]; exact h.rankP i hp hi
  case rankS =>
    intro i hp hi
    rw [hview i] at hi; rw [hnc]; exact h.rankS i hp hi
  case bmChildOK =>
    intro i ty b mj hvb
    rw [hviewBindI i] at hvb
    have hch := h.bmChildOK i ty b mj hvb
    exact ⟨by rw [hbmEq mj hch.1]; exact hch.1, hch.2.1, hch.2.2⟩
  case consP =>
    intro u i
    by_cases hb : u.bmOf = some m
    · rw [hpfNew u hb]
      exact ⟨fun hf => absurd hf (by simp), fun hx => (hnoView u i hb hx.1).elim⟩
    · have hne : ∀ mm, u.bmOf = some mm → mm ≠ m := by
        intro mm hmm hmm2; exact hb (hmm2 ▸ hmm)
      rw [hpfEq u hne, hview i]; exact h.consP u i
  case consS =>
    intro u i
    by_cases hb : u.bmOf = some m
    · rw [hsfNew u hb]
      exact ⟨fun hf => absurd hf (by simp), fun hx => (hnoView u i hb hx.1).elim⟩
    · have hne : ∀ mm, u.bmOf = some mm → mm ≠ m := by
        intro mm hmm hmm2; exact hb (hmm2 ▸ hmm)
      rw [hsfEq u hne, hview i]; exact h.consS u i
  case fresh =>
    intro u i hf
    by_cases hb : u.bmOf = some m
    · rw [hsfNew u hb] at hf; exact absurd hf (by simp)
    · have hne : ∀ mm, u.bmOf = some mm → mm ≠ m := by
        intro mm hmm hmm2; exact hb (hmm2 ▸ hmm)
      rw [hsfEq u hne] at hf; rw [hpfEq u hne]; exact h.fresh u i hf
  case bmConsP =>
    intro mm j
    rw [hpers, ← htb, ETables.findBM_pushBM]
    constructor
    · intro hf
      by_cases hk : m.pw = mm.pw
      · rw [if_pos hk, hid] at hf
        have hji : inew = j := Option.some.inj hf
        subst hji
        have hmm : mm = m := hpweq mm hk
        subst hmm
        exact ⟨hbmNew, hnp, htag0⟩
      · rw [if_neg hk] at hf
        obtain ⟨h1, h2, h3⟩ := (h.bmConsP mm j).mp hf
        exact ⟨hbmMono j mm h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      rcases hbmInv j mm h1 with hh | ⟨hix2, _, hmm3⟩
      · have hne : ¬ (m.pw = mm.pw) := by
          intro hk
          have hmm : mm = m := hpweq mm hk
          subst hmm
          rw [(h.bmConsP mm j).mpr ⟨hh, h2, h3⟩] at hfp; exact absurd hfp (by simp)
        rw [if_neg hne]
        exact (h.bmConsP mm j).mpr ⟨hh, h2, h3⟩
      · subst hmm3
        rw [if_pos rfl, hid]
        exact congrArg some (Idx.eq_of_idxNat (htag0.trans h3.symm)
          ((Idx.tier_eq_tierP hnp).trans (Idx.tier_eq_tierP h2).symm)
          (hix.trans hix2.symm))
  case bmConsS =>
    intro mm j
    rw [hscr]
    constructor
    · intro hf
      obtain ⟨h1, h2, h3⟩ := (h.bmConsS mm j).mp hf
      exact ⟨hbmMono j mm h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      rcases hbmInv j mm h1 with hh | ⟨_, hjp, _⟩
      · exact (h.bmConsS mm j).mpr ⟨hh, h2, h3⟩
      · rw [hjp] at h2; exact absurd h2 (by simp)
  case bmFresh =>
    intro mm j hf
    rw [hscr, hscrE, ETables.findBM_empty] at hf; exact absurd hf (by simp)
  case bmKeyP =>
    intro u mj i hf
    rw [hpers, ← htb, ETables.find?_pushBM] at hf
    rcases h.bmKeyP u mj i hf with h1 | ⟨m', h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨m', hpersFindBMmono m' mj h2⟩
  case bmKeyS =>
    intro u mj i hf
    rw [hscr] at hf
    rcases h.bmKeyS u mj i hf with h1 | ⟨m', h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨m', hfindBMmono m' mj h2⟩
  case derExact =>
    intro i u hi
    rw [hview i] at hi
    rw [hdov u, hder i]
    exact h.derExact i u hi
  case bmDerExact =>
    intro j mm hj
    rcases hbmInv j mm hj with hh | ⟨hix2, hjp0, hmm3⟩
    · have hbd : st'.bmDer j = st.bmDer j := by
        by_cases hjp : j.isPersistent = true
        · have hlt : j.idxNat < st.pers.bms.size := by
            rw [EStore.viewBM_pers hjp] at hh
            simp only [ETables.getBM] at hh
            exact Tbl.lt_of_map hh
          simp only [EStore.bmDer, EStore.persGetBMDer, hjp, if_true, hpers, ← htb,
            ETables.getBMDer_pushBM_of_lt (ETables.bms_Sized h.sizedP) hlt]
        · have hjp' : j.isPersistent = false := by simpa using hjp
          simp only [EStore.bmDer, EStore.persGetBMDer, hjp', hon, hon',
            Bool.false_eq_true, if_false]
      rw [hbd]; exact h.bmDerExact j mm hh
    · subst hmm3
      simp only [EStore.bmDer, EStore.persGetBMDer, hjp0, if_true, hpers, ← htb,
        ETables.getBMDer_pushBM_at_size (ETables.bms_Sized h.sizedP) hix2]
  case sizedP => rw [hpers, ← htb]; exact ETables.Sized_pushBM h.sizedP
  case sizedS => rw [hscr]; exact h.sizedS
  case capP =>
    intro u; rw [hpers, ← htb, ETables.sizeOf_pushBM]; exact h.capP u
  case capS => rw [hscr]; exact h.capS
  case bmCapP =>
    rw [hpers, ← htb, ETables.bmSize_pushBM, ETables.bmSize_eq]
    omega
  case bmCapS => rw [hscr]; exact h.bmCapS
  case scrOff => intro _; rw [hscr]; exact hscrE

/-! ### `internBM`, branch by branch

`intern`'s first step.  The four equations name its three outcomes — the
persistent hit, the scratch hit, and the two appends — so that no proof below
has to look inside the `match` twice. -/

theorem EStore.internBM_hit_pers {st : EStore} {m : ConLeche.BinderMeta}
    {i : BMIdx} (hi : st.persFindBM m = some i) : st.internBM m = (st, i) := by
  simp only [EStore.internBM, hi]

theorem EStore.internBM_hit_scr {st : EStore} {m : ConLeche.BinderMeta} {i : BMIdx}
    (hp : st.persFindBM m = none) (hon : st.scratchOn = true)
    (hi : st.scr.findBM m = some i) : st.internBM m = (st, i) := by
  simp only [EStore.internBM, hp, hon, if_true, hi]

theorem EStore.internBM_push_scr {st : EStore} {m : ConLeche.BinderMeta}
    (hp : st.persFindBM m = none) (hon : st.scratchOn = true)
    (hi : st.scr.findBM m = none) :
    st.internBM m =
      ({ st with scr := (st.scr.pushBM m (hash m.pw) Idx.tierS).1 },
        (st.scr.pushBM m (hash m.pw) Idx.tierS).2) := by
  simp only [EStore.internBM, hp, hon, if_true, hi]

theorem EStore.internBM_push_pers {st : EStore} {m : ConLeche.BinderMeta}
    (hp : st.persFindBM m = none) (hon : st.scratchOn = false) :
    st.internBM m =
      ({ st with pers := (st.pers.pushBM m (hash m.pw) Idx.tierP).1 },
        (st.pers.pushBM m (hash m.pw) Idx.tierP).2) := by
  simp only [EStore.internBM, hp, hon, Bool.false_eq_true, if_false]

/-- con-leche: none — arena infrastructure; **the datum's `intern_spec`**: the
store stays well formed, nothing a node read can see moves, and the handle it
answers decodes to the datum it was asked for. -/
theorem EStore.internBM_spec {st : EStore} {rk : EIdx → Nat}
    {m : ConLeche.BinderMeta} (h : EWFAt st rk) (hcap : st.capOKBM) :
    StoreWF (st.internBM m).1 ∧
      (st.internBM m).1.lss = st.lss ∧
      (st.internBM m).1.scratchOn = st.scratchOn ∧
      (∀ i : EIdx, (st.internBM m).1.view i = st.view i) ∧
      (∀ v : ENodeView, (st.internBM m).1.pers.sizeOf v = st.pers.sizeOf v) ∧
      (∀ v : ENodeView, (st.internBM m).1.scr.sizeOf v = st.scr.sizeOf v) ∧
      (st.internBM m).1.viewBM (st.internBM m).2 = some m ∧
      (st.internBM m).2.tag = 0 := by
  simp only [EStore.capOKBM] at hcap
  cases hp : st.persFindBM m with
  | some i =>
    rw [EStore.internBM_hit_pers hp]
    exact ⟨⟨rk, h⟩, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      ((h.bmConsP m i).mp hp).1, ((h.bmConsP m i).mp hp).2.2⟩
  | none =>
    cases hon : st.scratchOn with
    | true =>
      cases hs : st.scr.findBM m with
      | some i =>
        rw [EStore.internBM_hit_scr hp hon hs]
        exact ⟨⟨rk, h⟩, rfl, hon, fun _ => rfl, fun _ => rfl, fun _ => rfl,
          ((h.bmConsS m i).mp hs).1, ((h.bmConsS m i).mp hs).2.2⟩
      | none =>
        rw [hon] at hcap
        simp only [if_true] at hcap
        have hcap' : st.scr.bms.size < Idx.idxCap := hcap
        rw [EStore.internBM_push_scr hp hon hs]
        obtain ⟨hwf, hview, hbm, htg⟩ := EStore.wf_pushBM_scr
          (st' := { st with scr := (st.scr.pushBM m (hash m.pw) Idx.tierS).1 })
          (tb := (st.scr.pushBM m (hash m.pw) Idx.tierS).1)
          (inew := (st.scr.pushBM m (hash m.pw) Idx.tierS).2)
          h hon hon rfl rfl rfl rfl hcap' hp hs
        exact ⟨⟨rk, hwf⟩, rfl, hon, hview, fun _ => rfl,
          fun v => ETables.sizeOf_pushBM _ _ _ _ v, hbm, htg⟩
    | false =>
      rw [hon] at hcap
      simp only [Bool.false_eq_true, if_false] at hcap
      have hcap' : st.pers.bms.size < Idx.idxCap := hcap
      rw [EStore.internBM_push_pers hp hon]
      obtain ⟨hwf, hview, hbm, htg⟩ := EStore.wf_pushBM_pers
        (st' := { st with pers := (st.pers.pushBM m (hash m.pw) Idx.tierP).1 })
        (tb := (st.pers.pushBM m (hash m.pw) Idx.tierP).1)
        (inew := (st.pers.pushBM m (hash m.pw) Idx.tierP).2)
        h hon hon rfl rfl rfl rfl hcap' hp
      exact ⟨⟨rk, hwf⟩, rfl, hon, hview,
        fun v => ETables.sizeOf_pushBM _ _ _ _ v, fun _ => rfl, hbm, htg⟩

/-- con-leche: none — arena infrastructure; the same at the view `intern` is
interning: the datum handle the node's cons key will carry is exactly what
`findBMOfView` answers on the store the append then runs on. -/
theorem EStore.internBMOfView_spec {st : EStore} {rk : EIdx → Nat} {w : ENodeView}
    (h : EWFAt st rk) (hcap : EStore.eViewNeedsBM w = true → st.capOKBM) :
    StoreWF (st.internBMOfView w).1 ∧
      (st.internBMOfView w).1.lss = st.lss ∧
      (st.internBMOfView w).1.scratchOn = st.scratchOn ∧
      (∀ i : EIdx, (st.internBMOfView w).1.view i = st.view i) ∧
      (∀ v : ENodeView, (st.internBMOfView w).1.pers.sizeOf v = st.pers.sizeOf v) ∧
      (∀ v : ENodeView, (st.internBMOfView w).1.scr.sizeOf v = st.scr.sizeOf v) ∧
      ENodeView.BMOK (st.internBMOfView w).1.viewBM w (st.internBMOfView w).2 ∧
      (st.internBMOfView w).2.tag = 0 ∧
      (st.internBMOfView w).1.findBMOfView w = some (st.internBMOfView w).2 := by
  have hzero : (Idx.ofWord 0 : BMIdx).tag = 0 := by decide
  cases w
  case lam ty b m =>
    obtain ⟨hwf, h2, h3, h4, h5, h6, h7, h8⟩ := EStore.internBM_spec (m := m) h (hcap rfl)
    obtain ⟨rk1, hwf1⟩ := hwf
    have hbmok : ENodeView.BMOK (st.internBM m).1.viewBM (.lam ty b m)
        (st.internBM m).2 := by
      intro m' hm'
      simp only [ENodeView.bmOf, Option.some.injEq] at hm'
      subst hm'; exact h7
    exact ⟨⟨rk1, hwf1⟩, h2, h3, h4, h5, h6, hbmok, h8,
      by rw [EStore.findBMOfView_eq_findBM _ (rfl : (ENodeView.lam ty b m).bmOf = some m)]
         exact hwf1.findBM_of_viewBM h8 h7⟩
  case forallE ty b m =>
    obtain ⟨hwf, h2, h3, h4, h5, h6, h7, h8⟩ := EStore.internBM_spec (m := m) h (hcap rfl)
    obtain ⟨rk1, hwf1⟩ := hwf
    have hbmok : ENodeView.BMOK (st.internBM m).1.viewBM (.forallE ty b m)
        (st.internBM m).2 := by
      intro m' hm'
      simp only [ENodeView.bmOf, Option.some.injEq] at hm'
      subst hm'; exact h7
    exact ⟨⟨rk1, hwf1⟩, h2, h3, h4, h5, h6, hbmok, h8,
      by rw [EStore.findBMOfView_eq_findBM _
               (rfl : (ENodeView.forallE ty b m).bmOf = some m)]
         exact hwf1.findBM_of_viewBM h8 h7⟩
  all_goals exact ⟨⟨rk, h⟩, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    (by intro m' hm'; simp [ENodeView.bmOf] at hm'), hzero, rfl⟩

/-! ### `internAt`, and `intern` as its composite with `internBM`

`internAt` runs on the store `internBM` has already extended, at the datum
handle it answered — and `internBMOfView_spec`'s last conjunct is exactly what
makes that handle the one `findBMOfView` sees, so `consP`/`consS` apply to it
and the two appends are `wf_push_scr` / `wf_push_pers` unchanged. -/

/-- con-leche: none — arena infrastructure; `intern`'s node half. -/
theorem EStore.internAt_wf_view {st : EStore} {rk : EIdx → Nat} {w : ENodeView}
    {mi : BMIdx} (h : EWFAt st rk) (hsync : st.ScratchSync) (hv : st.ViewOK w)
    (hcap : (if st.scratchOn then st.scr.sizeOf w else st.pers.sizeOf w) < Idx.idxCap)
    (htag0 : mi.tag = 0) (hbmok : ENodeView.BMOK st.viewBM w mi)
    (hfov : st.findBMOfView w = some mi) :
    StoreWF (st.internAt w mi).1 ∧
      (st.internAt w mi).1.view (st.internAt w mi).2 = some w := by
  simp only [EStore.internAt]
  split
  · rename_i i hi
    have hpf : st.persFind? w = some i := by
      simp only [EStore.persFind?, hfov]; exact hi
    exact ⟨⟨rk, h⟩, ((h.consP w i).mp hpf).1⟩
  · rename_i hfp
    split
    · rename_i hon
      split
      · rename_i i hi
        have hsf : st.scrFind? w = some i := by
          simp only [EStore.scrFind?, hfov]; exact hi
        exact ⟨⟨rk, h⟩, ((h.consS w i).mp hsf).1⟩
      · rename_i hfs
        rw [if_pos hon] at hcap
        obtain ⟨hwf, hvw, _⟩ := EStore.wf_push_scr
          (st' := { st with scr := (st.scr.push w (st.derOfView w) mi Idx.tierS).1 })
          (tb := (st.scr.push w (st.derOfView w) mi Idx.tierS).1)
          (inew := (st.scr.push w (st.derOfView w) mi Idx.tierS).2)
          h hv hon hon rfl rfl htag0 hbmok rfl rfl hcap hfp hfs
        exact ⟨hwf, hvw⟩
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [if_neg hoff] at hcap
      obtain ⟨hwf, hvw, _⟩ := EStore.wf_push_pers
        (st' := { st with pers := (st.pers.push w (st.derOfView w) mi Idx.tierP).1 })
        (tb := (st.pers.push w (st.derOfView w) mi Idx.tierP).1)
        (inew := (st.pers.push w (st.derOfView w) mi Idx.tierP).2)
        h hv hsync hoff' hoff' rfl rfl htag0 hbmok rfl rfl hcap hfp
      exact ⟨hwf, hvw⟩

/-- con-leche: none — arena infrastructure; with the scratch tier off the node
half hands back a persistent handle.  Stated apart from `internAt_wf_view`
because `intern_isPersistent_of_off` does not assume `ViewOK`. -/
theorem EStore.internAt_isPersistent_of_off {st : EStore} {rk : EIdx → Nat}
    {w : ENodeView} {mi : BMIdx} (h : EWFAt st rk) (hoff : st.scratchOn = false)
    (hcap : st.pers.sizeOf w < Idx.idxCap)
    (hbmok : ENodeView.BMOK st.viewBM w mi)
    (hfov : st.findBMOfView w = some mi) :
    (st.internAt w mi).2.isPersistent = true := by
  simp only [EStore.internAt]
  split
  · rename_i i hi
    have hpf : st.persFind? w = some i := by
      simp only [EStore.persFind?, hfov]; exact hi
    exact ((h.consP w i).mp hpf).2
  · rw [if_neg (by simp [hoff])]
    show ((st.pers.push w (st.derOfView w) mi Idx.tierP).2).isPersistent = true
    show ((st.pers.push w (st.derOfView w) mi Idx.tierP).2).tier == 0
    rw [(ETables.getWith_push_spec st.pers st.viewBM w (st.derOfView w) mi Idx.tierP
      hbmok (by decide) hcap).2]
    decide

/-- con-leche: none — arena infrastructure; `intern` preserves the store
invariant and its handle decodes to the node interned.  The flag
synchronisation the persistent case needs is `EWFAt.sync` (task #97a); the
datum half is `internBM_spec` (task #97-LC). -/
theorem EStore.intern_wf_view_of_sync {st : EStore} {w : ENodeView} (h : StoreWF st)
    (_hsync : st.ScratchSync) (hv : st.ViewOK w) (hcap : st.capOK w) :
    StoreWF (st.intern w).1 ∧ (st.intern w).1.view (st.intern w).2 = some w := by
  obtain ⟨rk, h⟩ := h
  simp only [EStore.capOK] at hcap
  obtain ⟨hcapN, hcapB⟩ := hcap
  obtain ⟨hwf1, hlss1, hon1, hview1, hszP, hszS, hbmok, htag0, hfov1⟩ :=
    EStore.internBMOfView_spec h hcapB
  obtain ⟨rk1, h1⟩ := hwf1
  have hns1 : (st.internBMOfView w).1.ns = st.ns := by simp only [EStore.ns, hlss1]
  have hls1 : (st.internBMOfView w).1.ls = st.ls := by simp only [EStore.ls, hlss1]
  have hv1 : (st.internBMOfView w).1.ViewOK w := by
    refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
    · rw [hview1 c]; exact hv.expr c hc
    · rw [hns1]; exact hv.nm c hc
    · rw [hls1]; exact hv.lvl c hc
    · rw [hlss1]; exact hv.lst c hc
  have hcap1 : (if (st.internBMOfView w).1.scratchOn then
      (st.internBMOfView w).1.scr.sizeOf w
      else (st.internBMOfView w).1.pers.sizeOf w) < Idx.idxCap := by
    rw [hon1, hszP w, hszS w]; exact hcapN
  exact EStore.internAt_wf_view h1 h1.scratchSync hv1 hcap1 htag0 hbmok hfov1

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

theorem EStore.intern_spec_of_sync {st : EStore} {w : ENodeView} (h : StoreWF st)
    (hsync : st.ScratchSync) (hv : st.ViewOK w) (hcap : st.capOK w) :
    StoreWF (st.intern w).1 ∧ Ext st (st.intern w).1 ∧
      (st.intern w).1.view (st.intern w).2 = some w ∧
      denoteE (st.intern w).1 (st.intern w).2 = denoteEView (st.intern w).1 w := by
  have hwf := EStore.intern_wf_of_sync h hsync hv hcap
  have hview := EStore.intern_view_spec h hv hcap
  refine ⟨hwf, EStore.intern_ext st w, hview, ?_⟩
  obtain ⟨rk', hwf'⟩ := hwf
  exact denoteE_unfold hwf' hview


/-- With the scratch tier off, `intern` hands out a persistent handle. -/
theorem EStore.intern_isPersistent_of_off {st : EStore} {w : ENodeView}
    (h : StoreWF st) (hoff : st.scratchOn = false) (hcap : st.capOK w) :
    (st.intern w).2.isPersistent = true := by
  obtain ⟨rk, h⟩ := h
  simp only [EStore.capOK] at hcap
  obtain ⟨hcapN, hcapB⟩ := hcap
  obtain ⟨hwf1, hlss1, hon1, hview1, hszP, hszS, hbmok, htag0, hfov1⟩ :=
    EStore.internBMOfView_spec h hcapB
  obtain ⟨rk1, h1⟩ := hwf1
  have hoff1 : (st.internBMOfView w).1.scratchOn = false := by rw [hon1]; exact hoff
  have hcapN' : st.pers.sizeOf w < Idx.idxCap := by
    rw [hoff] at hcapN; simpa using hcapN
  have hcap1 : (st.internBMOfView w).1.pers.sizeOf w < Idx.idxCap := by
    rw [hszP w]; exact hcapN'
  exact EStore.internAt_isPersistent_of_off h1 hoff1 hcap1 hbmok hfov1

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
      LNodeView.param.injEq, beq_self_eq_true, reduceCtorEq, if_false,
      if_true] <;>
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
      LTag.imax, LTag.param, beq_self_eq_true, if_true] <;>
    (simp only [LTables.push]; exact Tbl.derAt_push_size (by assumption))

/-- con-leche: none — `LWFAt`'s `sync` clause, named (task #97a). -/
def LStore.ScratchSync (st : LStore) : Prop := st.scratchOn = st.ns.scratchOn

/-- con-leche: none — read the clause off the invariant. -/
theorem LWFAt.scratchSync {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    st.ScratchSync := h.sync

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
      · rw [if_pos hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
      · rw [if_neg hw] at hf
        obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consS u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfs] at hf; exact absurd hf (by simp)
        rw [if_neg hw]; exact hf
      · rw [if_pos rfl]
  case fresh =>
    intro u i hf
    rw [hscr, hfindtb u] at hf
    rw [hpers]
    by_cases hw : w = u
    · subst hw; exact hfp
    · rw [if_neg hw] at hf; exact h.fresh u i hf
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
      · rw [if_pos hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [if_neg hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [if_neg hw]; exact hf
      · rw [if_pos rfl]
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
        rw [if_pos hon] at hcap
        exact LStore.wf_push_scr h hv hon hon rfl rfl rfl rfl hcap hfp hfs
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [if_neg hoff] at hcap
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
      · rw [if_pos hon] at hcap
        have hspec := LTables.push_spec st.scr w (st.derOfView w) Idx.tierS
          (by decide) hcap
        have hp : ((st.scr.push w (st.derOfView w) Idx.tierS).2).isPersistent = false := by
          show (_ == 0) = false
          rw [hspec.2]; decide
        simp only [LStore.view]
        rw [if_neg (by simp [hp]), if_pos hon]
        exact hspec.1
    · rename_i hoff
      rw [if_neg hoff] at hcap
      have hspec := LTables.push_spec st.pers w (st.derOfView w) Idx.tierP
        (by decide) hcap
      have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [LStore.view]
      rw [if_pos hp]
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
        · rw [if_pos hp] at h ⊢; exact h
        · rw [if_neg hp] at h ⊢; exact LTables.get_push_mono _ _ _ _ h
    · rename_i hoff
      simp only [LStore.view, hoff] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [if_pos hp] at h ⊢; exact LTables.get_push_mono _ _ _ _ h
      · rw [if_neg hp] at h ⊢; exact h

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

theorem LsTables.get_eq_none_of_size {t : LsTables} {w : LsNodeView} {i : LsIdx}
    (htg : i.tag = LsTag.list) (hix : i.idxNat = t.sizeOf w) : t.get i = none := by
  simp only [LsTables.sizeOf] at hix
  simp [LsTables.get, htg, hix, Tbl.node?_size]

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

theorem LsTables.count_push {t : LsTables} {w : LsNodeView} {d : LDer} {tr : UInt32} :
    (t.push w d tr).1.count = t.count + 1 := by
  simp [LsTables.push, LsTables.count, Tbl.size_push]

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
  simp only [LsTables.derAt, htag, hix, beq_self_eq_true, if_true]
  simp only [LsTables.push]
  exact Tbl.derAt_push_size hs

/-- con-leche: none — the clause `LsStoreWF` is missing (task #97a). -/
def LsStore.ScratchSync (st : LsStore) : Prop := st.scratchOn = st.ls.scratchOn

/-- con-leche: none — read the clause off the invariant. -/
theorem LsWF.scratchSync {st : LsStore} (h : LsWF st) : st.ScratchSync := h.sync

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
      · rw [if_pos hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewS inew hnp]; exact hgetnew, hnp⟩
      · rw [if_neg hw] at hf
        obtain ⟨h1, h2⟩ := (h.consS u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consS u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfs] at hf; exact absurd hf (by simp)
        rw [if_neg hw]; exact hf
      · rw [if_pos rfl]
  case fresh =>
    intro u i hf
    rw [hscr, hfindtb u] at hf
    rw [hpers]
    by_cases hw : w = u
    · subst hw; exact hfp
    · rw [if_neg hw] at hf; exact h.fresh u i hf
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
      · rw [if_pos hw] at hf
        have hii : inew = i := Option.some.inj hf
        subst hii; subst hw
        exact ⟨by rw [hviewP inew hnp]; exact hgetnew, hnp⟩
      · rw [if_neg hw] at hf
        obtain ⟨h1, h2⟩ := (h.consP u i).mp hf
        exact ⟨hmono i u h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases hinv i u h1 with h3 | ⟨rfl, rfl⟩
      · have hf := (h.consP u i).mpr ⟨h3, h2⟩
        have hw : w ≠ u := by
          rintro rfl; rw [hfp] at hf; exact absurd hf (by simp)
        rw [if_neg hw]; exact hf
      · rw [if_pos rfl]
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
        rw [if_pos hon] at hcap
        exact LsStore.wf_push_scr h hv hon hon rfl rfl rfl rfl hcap hfp hfs
    · rename_i hoff
      have hoff' : st.scratchOn = false := by simpa using hoff
      rw [if_neg hoff] at hcap
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
      · rw [if_pos hon] at hcap
        have hspec := LsTables.push_spec st.scr w (st.derOfView w) Idx.tierS
          (by decide) hcap
        have hp : ((st.scr.push w (st.derOfView w) Idx.tierS).2).isPersistent = false := by
          show (_ == 0) = false
          rw [hspec.2]; decide
        simp only [LsStore.view]
        rw [if_neg (by simp [hp]), if_pos hon]
        exact hspec.1
    · rename_i hoff
      rw [if_neg hoff] at hcap
      have hspec := LsTables.push_spec st.pers w (st.derOfView w) Idx.tierP
        (by decide) hcap
      have hp : ((st.pers.push w (st.derOfView w) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [LsStore.view]
      rw [if_pos hp]
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
        · rw [if_pos hp] at h ⊢; exact h
        · rw [if_neg hp] at h ⊢; exact LsTables.get_push_mono _ _ _ _ h
    · rename_i hoff
      simp only [LsStore.view, hoff] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [if_pos hp] at h ⊢; exact LsTables.get_push_mono _ _ _ _ h
      · rw [if_neg hp] at h ⊢; exact h

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
    rw [EStore.view_dropScratch_pers st (h.bmPers i hp) hp, hv]; rfl
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

/-! ### `enableScratch`'s DENOTE half (task #97-P3-CoreWalks, the Checker
tier's ask 3)

`EStore.dropScratch_spec` carries three conjuncts — the invariant, the view
and **the denotation** — and `EStore.enableScratch_spec` carried only two.
The declaration bracket needs the third (`Bridge/Checker/**`'s
`PExt.enterScratch`: a pin handle interned before the prelude must still
denote after the scratch tier is opened), so here it is.

**The proof is one observation and no induction of its own.**
`enableScratch` and `dropScratch` differ in exactly one field, `scratchOn`,
and both set the scratch tier to `empty`.  A handle's `view` therefore does
not tell them apart: a persistent handle reads the same `pers` array in both,
and a scratch handle reads `none` in both — in `dropScratch` because the flag
is off, in `enableScratch` because the table it reads is empty.  So
`denote… st.enableScratch = denote… st.dropScratch` **as functions**, at all
four stores, and every `enableScratch` fact is the corresponding
`dropScratch` fact rewritten.  That is also why this is the honest way to
state it: the two operations really do have the same denotation, and the
`scratchOn` flag is about what `intern` will do NEXT, not about what the
store means. -/

theorem NStore.view_enableScratch_eq_dropScratch (st : NStore) (i : NIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  simp only [NStore.view, NStore.enableScratch, NStore.dropScratch]
  split
  · rfl
  · simp [NTables.get_empty]

theorem LStore.view_enableScratch_eq_dropScratch (st : LStore) (i : LIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  simp only [LStore.view, LStore.enableScratch, LStore.dropScratch]
  split
  · rfl
  · simp [LTables.get_empty]

theorem LsStore.view_enableScratch_eq_dropScratch (st : LsStore) (i : LsIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  simp only [LsStore.view, LsStore.enableScratch, LsStore.dropScratch]
  split
  · rfl
  · simp [LsTables.get_empty]

theorem EStore.viewBM_enableScratch_eq_dropScratch (st : EStore) (i : BMIdx) :
    st.enableScratch.viewBM i = st.dropScratch.viewBM i := by
  simp only [EStore.viewBM, EStore.enableScratch, EStore.dropScratch,
    EStore.persGetBM]
  split
  · rfl
  · simp [ETables.getBM_empty]

theorem EStore.viewBindI_enableScratch_eq_dropScratch (st : EStore) (i : EIdx) :
    st.enableScratch.viewBindI i = st.dropScratch.viewBindI i := by
  simp only [EStore.viewBindI, EStore.enableScratch, EStore.dropScratch,
    EStore.persGetBind]
  split
  · rfl
  · simp [ETables.getBind_empty]

theorem EStore.viewBind_enableScratch_eq_dropScratch (st : EStore) (i : EIdx) :
    st.enableScratch.viewBind i = st.dropScratch.viewBind i := by
  simp only [EStore.viewBind, EStore.viewBindI_enableScratch_eq_dropScratch,
    EStore.viewBM_enableScratch_eq_dropScratch]

theorem EStore.view_enableScratch_eq_dropScratch (st : EStore) (i : EIdx) :
    st.enableScratch.view i = st.dropScratch.view i := by
  simp only [EStore.view, EStore.viewBind_enableScratch_eq_dropScratch]
  split
  · rfl
  · simp only [EStore.enableScratch, EStore.dropScratch]
    split
    · rfl
    · simp [ETables.get_empty]

/-! The projections through the nesting, so that the congruences below can
rewrite with the store-level lemmas instead of unfolding the record. -/

theorem LStore.ns_enableScratch (st : LStore) :
    st.enableScratch.ns = st.ns.enableScratch := rfl
theorem LStore.ns_dropScratch (st : LStore) :
    st.dropScratch.ns = st.ns.dropScratch := rfl
theorem LsStore.ls_enableScratch (st : LsStore) :
    st.enableScratch.ls = st.ls.enableScratch := rfl
theorem LsStore.ls_dropScratch (st : LsStore) :
    st.dropScratch.ls = st.ls.dropScratch := rfl
theorem EStore.lss_enableScratch (st : EStore) :
    st.enableScratch.lss = st.lss.enableScratch := rfl
theorem EStore.lss_dropScratch (st : EStore) :
    st.dropScratch.lss = st.lss.dropScratch := rfl
theorem EStore.ls_enableScratch (st : EStore) :
    st.enableScratch.ls = st.ls.enableScratch := rfl
theorem EStore.ls_dropScratch (st : EStore) :
    st.dropScratch.ls = st.ls.dropScratch := rfl
theorem EStore.ns_enableScratch (st : EStore) :
    st.enableScratch.ns = st.ns.enableScratch := rfl
theorem EStore.ns_dropScratch (st : EStore) :
    st.dropScratch.ns = st.ns.dropScratch := rfl

theorem denoteNAux_enableScratch_eq (st : NStore) :
    ∀ (f : Nat) (i : NIdx),
      denoteNAux st.enableScratch f i = denoteNAux st.dropScratch f i := by
  intro f
  induction f with
  | zero => intro _; rfl
  | succ k ih =>
    intro i
    simp only [denoteNAux, NStore.view_enableScratch_eq_dropScratch, ih]

theorem denoteN_enableScratch_eq (st : NStore) (i : NIdx) :
    denoteN st.enableScratch i = denoteN st.dropScratch i := by
  show denoteNAux st.enableScratch (st.enableScratch.nodeCount + 1) i = _
  rw [denoteNAux_enableScratch_eq]
  rfl

theorem denoteLAux_enableScratch_eq (st : LStore) :
    ∀ (f : Nat) (i : LIdx),
      denoteLAux st.enableScratch f i = denoteLAux st.dropScratch f i := by
  intro f
  induction f with
  | zero => intro _; rfl
  | succ k ih =>
    intro i
    simp only [denoteLAux, LStore.view_enableScratch_eq_dropScratch, ih,
      LStore.ns_enableScratch, LStore.ns_dropScratch, denoteN_enableScratch_eq]

theorem denoteL_enableScratch_eq (st : LStore) (i : LIdx) :
    denoteL st.enableScratch i = denoteL st.dropScratch i := by
  show denoteLAux st.enableScratch (st.enableScratch.nodeCount + 1) i = _
  rw [denoteLAux_enableScratch_eq]
  rfl

theorem denoteLList_enableScratch_eq (st : LStore) :
    ∀ (us : List LIdx),
      denoteLList st.enableScratch us = denoteLList st.dropScratch us
  | [] => rfl
  | u :: us => by
    simp only [denoteLList, denoteL_enableScratch_eq,
      denoteLList_enableScratch_eq st us]

theorem denoteLs_enableScratch_eq (st : LsStore) (i : LsIdx) :
    denoteLs st.enableScratch i = denoteLs st.dropScratch i := by
  simp only [denoteLs, LsStore.view_enableScratch_eq_dropScratch,
    LsStore.ls_enableScratch, LsStore.ls_dropScratch,
    denoteLList_enableScratch_eq]

theorem denoteEAux_enableScratch_eq (st : EStore) :
    ∀ (f : Nat) (i : EIdx),
      denoteEAux st.enableScratch f i = denoteEAux st.dropScratch f i := by
  intro f
  induction f with
  | zero => intro _; rfl
  | succ k ih =>
    intro i
    simp only [denoteEAux, EStore.view_enableScratch_eq_dropScratch, ih,
      EStore.ls_enableScratch, EStore.ls_dropScratch, EStore.ns_enableScratch,
      EStore.ns_dropScratch, EStore.lss_enableScratch, EStore.lss_dropScratch,
      denoteL_enableScratch_eq, denoteN_enableScratch_eq,
      denoteLs_enableScratch_eq]

theorem denoteE_enableScratch_eq (st : EStore) (i : EIdx) :
    denoteE st.enableScratch i = denoteE st.dropScratch i := by
  show denoteEAux st.enableScratch (st.enableScratch.nodeCount + 1) i = _
  rw [denoteEAux_enableScratch_eq]
  rfl

/-- con-leche: none — arena infrastructure; **opening the scratch tier keeps
every persistent denotation**.  The `dropScratch` half has been there since
task #97a; this is its twin, and `Bridge/Checker/**`'s `PExt.enterScratch`
is what wanted it (task #97-P3-CoreWalks). -/
theorem EStore.enableScratch_denote_pers {st : EStore} (h : StoreWF st)
    {i : EIdx} {e : Expr} (hp : i.isPersistent = true)
    (hd : denoteE st i = some e) : denoteE st.enableScratch i = some e := by
  rw [denoteE_enableScratch_eq]
  exact EStore.dropScratch_denote_pers h hp hd

/-- con-leche: none — arena infrastructure; `EStore.enableScratch_spec` with
the denote conjunct `EStore.dropScratch_spec` has had all along. -/
theorem EStore.enableScratch_spec' {st : EStore} (h : StoreWF st) :
    StoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) ∧
      (∀ i e, i.isPersistent = true → denoteE st i = some e →
        denoteE st.enableScratch i = some e) ∧
      (∀ i, i.isPersistent = false → denoteE st.enableScratch i = none) :=
  ⟨EStore.enableScratch_wf h, fun _ hp => EStore.view_enableScratch_pers_wf h hp,
   fun _ _ hp hd => EStore.enableScratch_denote_pers h hp hd,
   fun _ hp => denoteE_enableScratch_scr st hp⟩

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

theorem NStore.enableScratch_spec {st : NStore} (h : NStoreWF st) :
    NStoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) := by
  obtain ⟨rk, h⟩ := h
  exact ⟨⟨rk, NStore.enableScratch_wfAt h⟩,
    fun _ hp => NStore.view_enableScratch_pers st hp⟩

theorem LStore.enableScratch_spec {st : LStore} (h : LStoreWF st) :
    LStoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) := by
  obtain ⟨rk, h⟩ := h
  exact ⟨⟨rk, LStore.enableScratch_wfAt h⟩,
    fun _ hp => LStore.view_enableScratch_pers st hp⟩

theorem LsStore.enableScratch_spec {st : LsStore} (h : LsStoreWF st) :
    LsStoreWF st.enableScratch ∧
      (∀ i, i.isPersistent = true → st.enableScratch.view i = st.view i) := by
  exact ⟨LsStore.enableScratch_wf h,
    fun _ hp => LsStore.view_enableScratch_pers st hp⟩

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
probe, whose cons key carries the binder datum's handle. -/
theorem EStore.find?_cases {st : EStore} {v : ENodeView} {i : EIdx}
    (hf : st.find? v = some i) :
    st.persFind? v = some i ∨ st.scrFind? v = some i := by
  simp only [EStore.find?] at hf
  split at hf
  · exact absurd hf (by simp)
  · rename_i mi hb
    simp only [EStore.findAt] at hf
    simp only [EStore.persFind?, EStore.scrFind?, hb]
    split at hf
    · rename_i j hp
      obtain rfl := Option.some.inj hf
      exact Or.inl hp
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

/-- con-leche: none — arena infrastructure; the PERSISTENT-tier probe, which
is what `internPersistentE` hits. -/
theorem EStore.view_of_persFind {st : EStore} {v : ENodeView} {i : EIdx}
    (h : StoreWF st) (hf : st.persFind? v = some i) : st.view i = some v := by
  obtain ⟨rk, hwf⟩ := h
  exact ((hwf.consP v i).mp hf).1

/-- con-leche: none — arena infrastructure; the name store's persistent
probe. -/
theorem NStore.view_of_persFind {st : NStore} {v : NNodeView} {i : NIdx}
    (h : NStoreWF st) (hf : st.pers.find? v = some i) : st.view i = some v := by
  obtain ⟨rk, hwf⟩ := h
  exact ((hwf.consP v i).mp hf).1

/-- con-leche: none — arena infrastructure; the level store's persistent
probe. -/
theorem LStore.view_of_persFind {st : LStore} {v : LNodeView} {i : LIdx}
    (h : LStoreWF st) (hf : st.pers.find? v = some i) : st.view i = some v := by
  obtain ⟨rk, hwf⟩ := h
  exact ((hwf.consP v i).mp hf).1

/-- con-leche: none — arena infrastructure; the level-list store's persistent
probe. -/
theorem LsStore.view_of_persFind {st : LsStore} {v : LsNodeView} {i : LsIdx}
    (h : LsStoreWF st) (hf : st.pers.find? v = some i) : st.view i = some v :=
  ((h.consP v i).mp hf).1


/-! ## ============================================================
    `Ext` at EVERY appending primitive — task #97a, follow-up 4

**This section is additive and self-contained, and it is the last thing in
the file.**  Task #97-P5-2 §10 and §11 item 4: `EStore.intern_ext` exists,
and `internBindI`, `internBM`, `internNNode`/`internLNode`/`internLsNode`,
the four `internPersistent`s and `promote` have no sibling — while
`Refine2`'s `AOut` demands `Ext lst.store lst'.store` at every one of them.
Five of Theorem 2's `intern_e_*_run` statements are blocked on the first of
those alone.

What was missing is not an argument — `EStore.intern_ext` is fifteen lines —
but the fact that the argument was written at ONE entry point and the store
has a dozen.  So it is factored here into four combinators
(`{N,L,Ls,}Ext.of_view_mono`) and then applied.  Every statement below is
**unconditional**: no `StoreWF`, no `ViewOK`, no `capOK`.  An append moves no
handle that decoded before it whatever the invariant says, and that is
precisely why the refinement can use these where it cannot use
`Bridge/StoreBind.lean`'s `internBindI_spec` or `Bridge/StoreNested.lean`'s
`internName_spec` — both of which assume the invariant, because they conclude
something about `view` as well, which `Ext` does not need.

The `promote` family's `Ext` is `Arena/PromoteExt.lean`: it is monadic, so it
needs `AState` and cannot be stated here. -/

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

`ETables.pushBind` (task #97-P6-16) appends a binder RECORD to the array its
tag names.  It touches `lams` or `foralls` and nothing else, so `get` — whose
two binder arms answer `none` — and `getBM` are literally unchanged, and only
`getBind` moves, exactly as under `push`.  These four are `push`'s lemmas at
that entry point. -/

theorem ETables.get_pushBind (t : ETables) (tag : UInt32) (r : BindNode) (d : UInt64)
    (tier : UInt32) (i : EIdx) : (t.pushBind tag r d tier).1.get i = t.get i := by
  unfold ETables.pushBind; split <;> rfl

theorem ETables.getBM_pushBind (t : ETables) (tag : UInt32) (r : BindNode) (d : UInt64)
    (tier : UInt32) (i : BMIdx) : (t.pushBind tag r d tier).1.getBM i = t.getBM i := by
  unfold ETables.pushBind; split <;> rfl

theorem ETables.getBind_pushBind_mono (t : ETables) (tag : UInt32) (r : BindNode)
    (d : UInt64) (tier : UInt32) {i : EIdx} {p : EIdx × EIdx × BMIdx}
    (h : t.getBind i = some p) : (t.pushBind tag r d tier).1.getBind i = some p := by
  refine ETables.getBind_mono ?_ ?_ h <;> intro n a ha <;>
    (simp only [ETables.pushBind]; split) <;>
    first | exact ha | exact Tbl.node?_push ha

theorem ETables.count_pushBind (t : ETables) (tag : UInt32) (r : BindNode) (d : UInt64)
    (tier : UInt32) : (t.pushBind tag r d tier).1.count = t.count + 1 := by
  unfold ETables.pushBind
  split <;> simp [ETables.count, Tbl.size_push] <;> omega

/-! ### `internBindI` — the binder append at a datum HANDLE

The lemma task #97-P5-2 §10 names as the ONE thing five of Theorem 2's
`intern_e_*_run` statements wait on: `Ext st (st.internBindI tag ty b mi).1`.
`Bridge/StoreBind.lean` gets it through `internBindI_eq_internAt`, which
needs a `BinderMeta` the datum handle decodes to and `StoreWF`'s
`bmDerExact`; `AOut`'s success arm has neither.  Taken directly on
`pushBind`, the fact is unconditional — an append moves no handle that
decoded before it, whatever the store's invariant says — which is the form
the refinement consumes. -/

/-- `internBindI`'s three outcomes: a cons hit moves nothing, a miss appends
the binder record to the tier the store is in. -/
theorem EStore.internBindI_cases (st : EStore) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) :
    (st.internBindI tag ty b mi).1 = st ∨
      (st.internBindI tag ty b mi).1 =
        { st with scr := (st.scr.pushBind tag ⟨ty, b, mi⟩
            (st.derOfBindAtI (if tag == ETag.lam then 19 else 23) ty b mi)
            Idx.tierS).1 } ∨
      (st.internBindI tag ty b mi).1 =
        { st with pers := (st.pers.pushBind tag ⟨ty, b, mi⟩
            (st.derOfBindAtI (if tag == ETag.lam then 19 else 23) ty b mi)
            Idx.tierP).1 } := by
  simp only [EStore.internBindI]
  split
  · exact Or.inl rfl
  · split
    · split
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem EStore.view_internBindI_mono (st : EStore) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) {i : EIdx} {v : ENodeView} (h : st.view i = some v) :
    (st.internBindI tag ty b mi).1.view i = some v := by
  rcases EStore.internBindI_cases st tag ty b mi with he | he | he <;> rw [he]
  · exact h
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => by rw [ETables.get_pushBind]; exact hh
    · exact fun _ _ hh => ETables.getBind_pushBind_mono _ _ _ _ _ hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => hk
      · exact fun _ _ hk => by rw [ETables.getBM_pushBind]; exact hk
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => by rw [ETables.get_pushBind]; exact hh
    · exact fun _ _ hh => ETables.getBind_pushBind_mono _ _ _ _ _ hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => by rw [ETables.getBM_pushBind]; exact hk
      · exact fun _ _ hk => hk

theorem EStore.lss_internBindI (st : EStore) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) : (st.internBindI tag ty b mi).1.lss = st.lss := by
  rcases EStore.internBindI_cases st tag ty b mi with he | he | he <;> rw [he]

theorem EStore.scratchOn_internBindI (st : EStore) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) : (st.internBindI tag ty b mi).1.scratchOn = st.scratchOn := by
  rcases EStore.internBindI_cases st tag ty b mi with he | he | he <;> rw [he]

theorem EStore.nodeCount_internBindI_le (st : EStore) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) : st.nodeCount ≤ (st.internBindI tag ty b mi).1.nodeCount := by
  rcases EStore.internBindI_cases st tag ty b mi with he | he | he <;> rw [he]
  · exact Nat.le_refl _
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_pushBind]
    omega
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_pushBind]
    omega

/-! ### The persistent-tier appends

`internBMPersistent`, `internBMOfViewPersistent` and `EStore.internPersistent`
(task #97-P6-2): `intern`'s `else` branch with the scratch probe left out, so
the append lands in `pers` whatever tier the store is in.  `Ext` does not care
which tier grew — it is `view` monotonicity and a node count — so these are
the same three lines as their `intern` siblings.  (The INVARIANT does care:
`fresh` is transiently broken by a promotion, which is why `Bridge`'s
`StoreWFP` exists.  Nothing here touches that; `Ext` is the conjunct the
promotion keeps outright.) -/

theorem EStore.internBMPersistent_cases (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBMPersistent m).1 = st ∨
      (st.internBMPersistent m).1 =
        { st with pers := (st.pers.pushBM m (hash m.pw) Idx.tierP).1 } := by
  simp only [EStore.internBMPersistent]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem EStore.view_internBMPersistent_mono (st : EStore) (m : ConLeche.BinderMeta)
    {i : EIdx} {v : ENodeView} (h : st.view i = some v) :
    (st.internBMPersistent m).1.view i = some v := by
  rcases EStore.internBMPersistent_cases st m with he | he <;> rw [he]
  · exact h
  · refine EStore.view_mono_of_tiers st _ ?_ ?_ ?_ ?_ ?_ ?_ h
    · rfl
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers st _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => ETables.getBM_pushBM_mono hk
      · exact fun _ _ hk => hk

theorem EStore.lss_internBMPersistent (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBMPersistent m).1.lss = st.lss := by
  rcases EStore.internBMPersistent_cases st m with he | he <;> rw [he]

theorem EStore.scratchOn_internBMPersistent (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBMPersistent m).1.scratchOn = st.scratchOn := by
  rcases EStore.internBMPersistent_cases st m with he | he <;> rw [he]

theorem EStore.nodeCount_internBMPersistent (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBMPersistent m).1.nodeCount = st.nodeCount := by
  rcases EStore.internBMPersistent_cases st m with he | he <;> rw [he] <;>
    simp [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.count_pushBM]

theorem EStore.view_internBMOfViewPersistent_mono (st : EStore) (w : ENodeView)
    {i : EIdx} {v : ENodeView} (h : st.view i = some v) :
    (st.internBMOfViewPersistent w).1.view i = some v := by
  cases w
  case lam _ _ m => exact EStore.view_internBMPersistent_mono st m h
  case forallE _ _ m => exact EStore.view_internBMPersistent_mono st m h
  all_goals exact h

theorem EStore.lss_internBMOfViewPersistent (st : EStore) (w : ENodeView) :
    (st.internBMOfViewPersistent w).1.lss = st.lss := by
  cases w
  case lam _ _ m => exact EStore.lss_internBMPersistent st m
  case forallE _ _ m => exact EStore.lss_internBMPersistent st m
  all_goals rfl

theorem EStore.scratchOn_internBMOfViewPersistent (st : EStore) (w : ENodeView) :
    (st.internBMOfViewPersistent w).1.scratchOn = st.scratchOn := by
  cases w
  case lam _ _ m => exact EStore.scratchOn_internBMPersistent st m
  case forallE _ _ m => exact EStore.scratchOn_internBMPersistent st m
  all_goals rfl

theorem EStore.nodeCount_internBMOfViewPersistent (st : EStore) (w : ENodeView) :
    (st.internBMOfViewPersistent w).1.nodeCount = st.nodeCount := by
  cases w
  case lam _ _ m => exact EStore.nodeCount_internBMPersistent st m
  case forallE _ _ m => exact EStore.nodeCount_internBMPersistent st m
  all_goals rfl

theorem EStore.internPersistent_cases (st : EStore) (v : ENodeView) :
    (st.internPersistent v).1 = (st.internBMOfViewPersistent v).1 ∨
      (st.internPersistent v).1 =
        { (st.internBMOfViewPersistent v).1 with
            pers := ((st.internBMOfViewPersistent v).1.pers.push v
              ((st.internBMOfViewPersistent v).1.derOfView v)
              (st.internBMOfViewPersistent v).2 Idx.tierP).1 } := by
  simp only [EStore.internPersistent]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem EStore.view_internPersistent_mono (st : EStore) (w : ENodeView)
    {i : EIdx} {v : ENodeView} (h : st.view i = some v) :
    (st.internPersistent w).1.view i = some v := by
  have h0 := EStore.view_internBMOfViewPersistent_mono st w h
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he]
  · exact h0
  · refine EStore.view_mono_of_tiers _ _ ?_ ?_ ?_ ?_ ?_ ?_ h0
    · rfl
    · exact fun _ _ hh => ETables.get_push_mono _ _ _ _ _ hh
    · exact fun _ _ hh => ETables.getBind_push_mono _ _ _ _ _ hh
    · exact fun _ _ hh => hh
    · exact fun _ _ hh => hh
    · intro j mm hh
      refine EStore.viewBM_mono_of_tiers _ _ ?_ ?_ ?_ hh
      · rfl
      · exact fun _ _ hk => by rw [ETables.getBM_push]; exact hk
      · exact fun _ _ hk => hk

theorem EStore.lss_internPersistent (st : EStore) (w : ENodeView) :
    (st.internPersistent w).1.lss = st.lss := by
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he] <;>
    exact EStore.lss_internBMOfViewPersistent st w

theorem EStore.scratchOn_internPersistent (st : EStore) (w : ENodeView) :
    (st.internPersistent w).1.scratchOn = st.scratchOn := by
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he] <;>
    exact EStore.scratchOn_internBMOfViewPersistent st w

theorem EStore.nodeCount_internPersistent_le (st : EStore) (w : ENodeView) :
    st.nodeCount ≤ (st.internPersistent w).1.nodeCount := by
  have h0 := EStore.nodeCount_internBMOfViewPersistent st w
  rcases EStore.internPersistent_cases st w with he | he <;> rw [he]
  · omega
  · simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount,
      ETables.count_push]
    simp only [EStore.nodeCount, EStore.persCount, EStore.scrCount] at h0
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
    · rw [if_pos hp] at h ⊢; exact NTables.get_push_mono _ _ _ _ h
    · rw [if_neg hp] at h ⊢; exact h

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
    · rw [if_pos hp] at h ⊢; exact LTables.get_push_mono _ _ _ _ h
    · rw [if_neg hp] at h ⊢; exact h

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
    · rw [if_pos hp] at h ⊢; exact LsTables.get_push_mono _ _ _ _ h
    · rw [if_neg hp] at h ⊢; exact h

theorem LsStore.scratchOn_internPersistent (st : LsStore) (w : LsNodeView) :
    (st.internPersistent w).1.scratchOn = st.scratchOn := by
  rcases LsStore.internPersistent_cases st w with he | he <;> rw [he]

/-! ### The `Ext` theorems, one per appending entry point

Each is `…Ext.of_view_mono` at the three plumbing lemmas above it.  Together
with `EStore.intern_ext` they cover every primitive of `Store.lean` that
appends: the four node stores' `intern` and `internPersistent`, the datum
store's `internBM` and `internBMPersistent`, the binder entry `internBindI`
and its four faces, and the six lifts through the nesting. -/

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

/-- con-leche: none — arena infrastructure; `intern`'s node half on its own —
`intern_ext`'s argument with `internBMOfView` removed. -/
theorem EStore.internAt_ext (st : EStore) (w : ENodeView) (mi : BMIdx) :
    Ext st (st.internAt w mi).1 :=
  Ext.of_view_mono (by rw [EStore.lss_internAt]; exact LsExt.refl _)
    (fun _ _ h => EStore.view_internAt_mono st w mi h)
    (EStore.nodeCount_internAt_le st w mi)

theorem EStore.lss_internBM (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBM m).1.lss = st.lss := by
  rcases EStore.internBM_cases st m with he | he | he <;> rw [he]

theorem EStore.scratchOn_internBM (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBM m).1.scratchOn = st.scratchOn := by
  rcases EStore.internBM_cases st m with he | he | he <;> rw [he]

theorem EStore.nodeCount_internBM (st : EStore) (m : ConLeche.BinderMeta) :
    (st.internBM m).1.nodeCount = st.nodeCount := by
  rcases EStore.internBM_cases st m with he | he | he <;> rw [he] <;>
    simp [EStore.nodeCount, EStore.persCount, EStore.scrCount, ETables.count_pushBM]

/-- con-leche: none — arena infrastructure; the binder DATUM's append extends
the arena.  It moves no node read at all, so the node count stands still. -/
theorem EStore.internBM_ext (st : EStore) (m : ConLeche.BinderMeta) :
    Ext st (st.internBM m).1 :=
  Ext.of_view_mono (by rw [EStore.lss_internBM]; exact LsExt.refl _)
    (fun _ _ h => EStore.view_internBM_mono st m h)
    (by rw [EStore.nodeCount_internBM]; exact Nat.le_refl _)

theorem EStore.internBMOfView_ext (st : EStore) (w : ENodeView) :
    Ext st (st.internBMOfView w).1 :=
  Ext.of_view_mono (by rw [EStore.lss_internBMOfView]; exact LsExt.refl _)
    (fun _ _ h => EStore.view_internBMOfView_mono st w h)
    (by rw [EStore.nodeCount_internBMOfView]; exact Nat.le_refl _)

theorem EStore.internBMPersistent_ext (st : EStore) (m : ConLeche.BinderMeta) :
    Ext st (st.internBMPersistent m).1 :=
  Ext.of_view_mono (by rw [EStore.lss_internBMPersistent]; exact LsExt.refl _)
    (fun _ _ h => EStore.view_internBMPersistent_mono st m h)
    (by rw [EStore.nodeCount_internBMPersistent]; exact Nat.le_refl _)

theorem EStore.internBMOfViewPersistent_ext (st : EStore) (w : ENodeView) :
    Ext st (st.internBMOfViewPersistent w).1 :=
  Ext.of_view_mono (by rw [EStore.lss_internBMOfViewPersistent]; exact LsExt.refl _)
    (fun _ _ h => EStore.view_internBMOfViewPersistent_mono st w h)
    (by rw [EStore.nodeCount_internBMOfViewPersistent]; exact Nat.le_refl _)

/-- con-leche: none — arena infrastructure; **the binder append extends the
arena** (task #97-P5-2 §10, §11 item 4).  Unconditional: no `StoreWF`, no
`BinderMeta`, no capacity — which is what `Refine2`'s `AOut` needs of it. -/
theorem EStore.internBindI_ext (st : EStore) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) : Ext st (st.internBindI tag ty b mi).1 :=
  Ext.of_view_mono (by rw [EStore.lss_internBindI]; exact LsExt.refl _)
    (fun _ _ h => EStore.view_internBindI_mono st tag ty b mi h)
    (EStore.nodeCount_internBindI_le st tag ty b mi)

theorem EStore.internLamI_ext (st : EStore) (ty b : EIdx) (mi : BMIdx) :
    Ext st (st.internLamI ty b mi).1 := EStore.internBindI_ext st _ ty b mi

theorem EStore.internForallEI_ext (st : EStore) (ty b : EIdx) (mi : BMIdx) :
    Ext st (st.internForallEI ty b mi).1 := EStore.internBindI_ext st _ ty b mi

theorem EStore.internEBindI_ext (st : EStore) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) : Ext st (st.internEBindI tag ty b mi).1 :=
  EStore.internBindI_ext st tag ty b mi

theorem EStore.internLam_ext (st : EStore) (ty b : EIdx) (m : ConLeche.BinderMeta) :
    Ext st (st.internLam ty b m).1 :=
  (EStore.internBM_ext st m).trans
    (EStore.internLamI_ext (st.internBM m).1 ty b (st.internBM m).2)

theorem EStore.internForallE_ext (st : EStore) (ty b : EIdx)
    (m : ConLeche.BinderMeta) : Ext st (st.internForallE ty b m).1 :=
  (EStore.internBM_ext st m).trans
    (EStore.internForallEI_ext (st.internBM m).1 ty b (st.internBM m).2)

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

theorem EStore.view_internName (st : EStore) (w : NNodeView) (i : EIdx) :
    (st.internName w).1.view i = st.view i := rfl
theorem EStore.view_internLevel (st : EStore) (w : LNodeView) (i : EIdx) :
    (st.internLevel w).1.view i = st.view i := rfl
theorem EStore.view_internLevels (st : EStore) (w : LsNodeView) (i : EIdx) :
    (st.internLevels w).1.view i = st.view i := rfl
theorem EStore.view_internNamePersistent (st : EStore) (w : NNodeView) (i : EIdx) :
    (st.internNamePersistent w).1.view i = st.view i := rfl
theorem EStore.view_internLevelPersistent (st : EStore) (w : LNodeView) (i : EIdx) :
    (st.internLevelPersistent w).1.view i = st.view i := rfl
theorem EStore.view_internLevelsPersistent (st : EStore) (w : LsNodeView) (i : EIdx) :
    (st.internLevelsPersistent w).1.view i = st.view i := rfl

theorem EStore.scratchOn_internName (st : EStore) (w : NNodeView) :
    (st.internName w).1.scratchOn = st.scratchOn := rfl
theorem EStore.scratchOn_internLevel (st : EStore) (w : LNodeView) :
    (st.internLevel w).1.scratchOn = st.scratchOn := rfl
theorem EStore.scratchOn_internLevels (st : EStore) (w : LsNodeView) :
    (st.internLevels w).1.scratchOn = st.scratchOn := rfl
theorem EStore.scratchOn_internNamePersistent (st : EStore) (w : NNodeView) :
    (st.internNamePersistent w).1.scratchOn = st.scratchOn := rfl
theorem EStore.scratchOn_internLevelPersistent (st : EStore) (w : LNodeView) :
    (st.internLevelPersistent w).1.scratchOn = st.scratchOn := rfl
theorem EStore.scratchOn_internLevelsPersistent (st : EStore) (w : LsNodeView) :
    (st.internLevelsPersistent w).1.scratchOn = st.scratchOn := rfl


end ConRon.Arena
