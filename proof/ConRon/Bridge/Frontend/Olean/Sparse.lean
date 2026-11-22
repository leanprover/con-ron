/-
# `ConRon.Bridge.Frontend.Olean.Sparse` — the sparse decoder, Theorem 1 (task #166)

**A memo whose every value denotes the specification's at its location stays so** under the
twin's sparse read `sGo` (`sparseGo_run`), and the read holds what it was asked for.  `SparseGood` is the
invariant: per kind, a memo's handle denotes `nameAt`/`levelAt`/`levelsAt`/`exprAt` at its
location; the frontier is `FrontierGood` (`Bridge/Frontend/Olean/Closure.lean`).  Each object is
built by its node function over the memo (`nameNode_run` …, `Bridge/Frontend/Olean/Nodes.lean`),
its kids held by the kid walk (`kidsGo_run`).  So a name read sparsely (`sparseNameP_run`) is
upstream's `nameP`.  Run style (a simulation by strong induction), not `vcgen`.
-/
module

public import ConRon.Bridge.Frontend.Olean.Closure
public import ConRon.Bridge.Frontend.Olean.Nodes
public import ConRon.Arena.Frontend.Olean.Sparse
import ConLeche.Verify.Frontend.Olean.Sparse
import Std.Data.HashMap.Lemmas

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins SM Frontier)
open ConLeche.Frontend.Olean (Region Kid kName kLevel kLevels kExpr kidTable nameAt levelAt levelsAt
  exprAt IsKind lookup)

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:81 SM.Good — **a memo of handles that
denote the specification's values** at their locations. -/
structure SparseGood (st : EStore) (r : Region) (m : SM) : Prop where
  names : ∀ c x, m.names[c]? = some x → ∃ n, nameAt r c = some n ∧ denoteN st.ns x = some n
  levels : ∀ c x, m.levels[c]? = some x → ∃ u, levelAt r c = some u ∧ denoteL st.ls x = some u
  lists : ∀ c x, m.lists[c]? = some x → ∃ us, levelsAt r c = some us ∧ denoteLs st.lss x = some us
  exprs : ∀ c x, m.exprs[c]? = some x → ∃ e, exprAt r c = some e ∧ denoteE st x = some e

theorem SparseGood.empty (st : EStore) (r : Region) : SparseGood st r {} :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h,
    fun _ _ h => by simp at h⟩

theorem SparseGood.ext {st st' : EStore} {r : Region} {m : SM} (h : SparseGood st r m) (hx : Ext st st') :
    SparseGood st' r m :=
  ⟨fun c x hc => let ⟨n, a, b⟩ := h.names c x hc; ⟨n, a, denoteN_ext b hx⟩,
   fun c x hc => let ⟨n, a, b⟩ := h.levels c x hc; ⟨n, a, denoteL_ext b hx⟩,
   fun c x hc => let ⟨n, a, b⟩ := h.lists c x hc; ⟨n, a, denoteLs_ext b hx⟩,
   fun c x hc => let ⟨n, a, b⟩ := h.exprs c x hc; ⟨n, a, denote_ext b hx⟩⟩

/-! ## Lookups -/

theorem sparseLookup_good {α : Type} {m : Std.HashMap Nat α} {t : ConLeche.Frontend.Olean.Table α}
    {P : Nat → α → Prop} (hm : ∀ c x, m[c]? = some x → P c x) (ht : TableRel P t) {c : Nat}
    {x : α} (h : lookup m t c = some x) : P c x := by
  unfold lookup at h
  split at h
  · rename_i v hv
    cases h
    exact hm c _ hv
  · exact ht.get h

theorem lookup_isSome {α : Type} {m : Std.HashMap Nat α} {t : ConLeche.Frontend.Olean.Table α}
    {c : Nat} (h : m.contains c = true ∨ (t.get c).isSome = true) : (lookup m t c).isSome = true := by
  unfold lookup
  split
  · rfl
  · rename_i hv
    rcases h with h | h
    · rw [Std.HashMap.contains_eq_isSome_getElem?, hv] at h
      cases h
    · exact h

/-- The memo over the frontier as a node's `sub` denotes at every location it answers. -/
theorem subIn_good {st : EStore} {r : Region} {m : SM} {b : Frontier} (hm : SparseGood st r m)
    (hb : FrontierGood st r b) (k : UInt8) (g : Nat)
    (hk : ∀ k' c, Kid r k g k' c → m.holds b k' c = true) :
    SubRel st r k g (m.subIn b) (fun c _ => exprAt r c) (fun c _ => nameAt r c)
      (fun c _ => levelAt r c) (fun c _ => levelsAt r c) := by
  have hne1 : kName ≠ kLevel := by decide
  have hne2 : kName ≠ kLevels := by decide
  have hne3 : kLevel ≠ kLevels := by decide
  have hne4 : kExpr ≠ kName := by decide
  have hne5 : kExpr ≠ kLevel := by decide
  have hne6 : kExpr ≠ kLevels := by decide
  refine ⟨fun c _ hc => ?_, fun c _ hc => ?_, fun c _ hc => ?_, fun c _ hc => ?_⟩
  · have hh := hk _ _ hc
    simp only [SM.holds, SM.has, Frontier.has, ↓reduceIte] at hh
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (lookup_isSome (Bool.or_eq_true _ _ ▸ hh))
    obtain ⟨n, h1, h2⟩ := sparseLookup_good hm.names hb.names hx
    exact ⟨x, n, hx, h2, h1⟩
  · have hh := hk _ _ hc
    simp only [SM.holds, SM.has, Frontier.has, hne1.symm, ↓reduceIte] at hh
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (lookup_isSome (Bool.or_eq_true _ _ ▸ hh))
    obtain ⟨n, h1, h2⟩ := sparseLookup_good hm.levels hb.levels hx
    exact ⟨x, n, hx, h2, h1⟩
  · have hh := hk _ _ hc
    simp only [SM.holds, SM.has, Frontier.has, hne2.symm, hne3.symm, ↓reduceIte] at hh
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (lookup_isSome (Bool.or_eq_true _ _ ▸ hh))
    obtain ⟨n, h1, h2⟩ := sparseLookup_good hm.lists hb.lists hx
    exact ⟨x, n, hx, h2, h1⟩
  · have hh := hk _ _ hc
    simp only [SM.holds, SM.has, Frontier.has, hne4, hne5, hne6, ↓reduceIte] at hh
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (lookup_isSome (Bool.or_eq_true _ _ ▸ hh))
    obtain ⟨n, h1, h2⟩ := sparseLookup_good hm.exprs hb.exprs hx
    exact ⟨x, n, hx, h2, h1⟩

/-! ## The walk -/

/-- What a read keeps: everything the memo or the frontier held. -/
@[expose] def SMKeeps (b : Frontier) (m m' : SM) : Prop :=
  ∀ k c, m.holds b k c = true → m'.holds b k c = true

theorem SMKeeps.refl (b : Frontier) (m : SM) : SMKeeps b m m := fun _ _ h => h

theorem SMKeeps.trans {b : Frontier} {m₁ m₂ m₃ : SM} (h₁ : SMKeeps b m₁ m₂) (h₂ : SMKeeps b m₂ m₃) :
    SMKeeps b m₁ m₃ := fun k c h => h₂ k c (h₁ k c h)

theorem holds_names {b : Frontier} {m : SM} {g : Nat} {v : NIdx} :
    ({ m with names := m.names.insert g v } : SM).holds b kName g = true := by
  simp [SM.holds, SM.has, Std.HashMap.contains_insert]

theorem keeps_names {b : Frontier} {m : SM} {g : Nat} {v : NIdx} :
    SMKeeps b m { m with names := m.names.insert g v } := by
  intro k c h
  simp only [SM.holds, SM.has] at h ⊢
  by_cases h1 : k = kName <;> by_cases h2 : k = kLevel <;> by_cases h3 : k = kLevels <;>
    simp_all [Std.HashMap.contains_insert] <;>
    rcases h with h | h <;> simp [h]

theorem holds_levels {b : Frontier} {m : SM} {g : Nat} {v : LIdx} :
    ({ m with levels := m.levels.insert g v } : SM).holds b kLevel g = true := by
  have : kLevel ≠ kName := by decide
  simp [SM.holds, SM.has, this, Std.HashMap.contains_insert]

theorem keeps_levels {b : Frontier} {m : SM} {g : Nat} {v : LIdx} :
    SMKeeps b m { m with levels := m.levels.insert g v } := by
  intro k c h
  simp only [SM.holds, SM.has] at h ⊢
  by_cases h1 : k = kName <;> by_cases h2 : k = kLevel <;> by_cases h3 : k = kLevels <;>
    simp_all [Std.HashMap.contains_insert] <;>
    rcases h with h | h <;> simp [h]

theorem holds_lists {b : Frontier} {m : SM} {g : Nat} {v : LsIdx} :
    ({ m with lists := m.lists.insert g v } : SM).holds b kLevels g = true := by
  have h1 : kLevels ≠ kName := by decide
  have h2 : kLevels ≠ kLevel := by decide
  simp [SM.holds, SM.has, h1, h2, Std.HashMap.contains_insert]

theorem keeps_lists {b : Frontier} {m : SM} {g : Nat} {v : LsIdx} :
    SMKeeps b m { m with lists := m.lists.insert g v } := by
  intro k c h
  simp only [SM.holds, SM.has] at h ⊢
  by_cases h1 : k = kName <;> by_cases h2 : k = kLevel <;> by_cases h3 : k = kLevels <;>
    simp_all [Std.HashMap.contains_insert] <;>
    rcases h with h | h <;> simp [h]

theorem holds_exprs {b : Frontier} {m : SM} {g : Nat} {v : EIdx} :
    ({ m with exprs := m.exprs.insert g v } : SM).holds b kExpr g = true := by
  have h1 : kExpr ≠ kName := by decide
  have h2 : kExpr ≠ kLevel := by decide
  have h3 : kExpr ≠ kLevels := by decide
  simp [SM.holds, SM.has, h1, h2, h3, Std.HashMap.contains_insert]

theorem keeps_exprs {b : Frontier} {m : SM} {g : Nat} {v : EIdx} :
    SMKeeps b m { m with exprs := m.exprs.insert g v } := by
  intro k c h
  simp only [SM.holds, SM.has] at h ⊢
  by_cases h1 : k = kName <;> by_cases h2 : k = kLevel <;> by_cases h3 : k = kLevels <;>
    simp_all [Std.HashMap.contains_insert] <;>
    rcases h with h | h <;> simp [h]

theorem getElem?_insert_good {α : Type} {m : Std.HashMap Nat α} {g : Nat} {v : α}
    {P : Nat → α → Prop} (hm : ∀ c x, m[c]? = some x → P c x) (hv : P g v) :
    ∀ c x, (m.insert g v)[c]? = some x → P c x := by
  intro c x h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i he
    simp only [beq_iff_eq] at he
    subst he
    cases h
    exact hv
  · exact hm c x h

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:159-182 SM.buildIn — **the object built over a
memo holding its kids is the specification's**, added to the memo. -/
theorem sparseBuildIn_run {pk : OleanPins} {r : Region} {b : Frontier} {k : UInt8} {g : Nat} {m m' : SM}
    {s s' : AState} (hok : StateOK s) (hpk : NullsRel s.store pk) (hk : IsKind k)
    (hm : SparseGood s.store r m) (hb : FrontierGood s.store r b)
    (hkids : ∀ k' c, Kid r k g k' c → m.holds b k' c = true)
    (h : ConRon.Arena.Frontend.Olean.SM.buildIn pk r b k g m s = .ok (some m', s')) :
    ParseStep s s' ∧ SparseGood s'.store r m' ∧ m'.holds b k g = true ∧ SMKeeps b m m' := by
  have hsub := subIn_good hm hb k g hkids
  unfold ConRon.Arena.Frontend.Olean.SM.buildIn at h
  rcases hk with rfl | rfl | rfl | rfl
  · simp only [↓reduceIte] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
      cases hv
      obtain ⟨hst, n, hn, hd⟩ := nameNode_run hok hpk hsub h1
      have hg := hm.ext hst.ext
      refine ⟨hst, ⟨getElem?_insert_good hg.names ⟨n, by rw [nameAt]; exact hn, hd⟩, hg.levels,
        hg.lists, hg.exprs⟩, holds_names, keeps_names⟩
  · have : kLevel ≠ kName := by decide
    simp only [this, ↓reduceIte] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
      cases hv
      obtain ⟨hst, n, hn, hd⟩ := levelNode_run hok hpk hsub h1
      have hg := hm.ext hst.ext
      refine ⟨hst, ⟨hg.names, getElem?_insert_good hg.levels ⟨n, by rw [levelAt]; exact hn, hd⟩,
        hg.lists, hg.exprs⟩, holds_levels, keeps_levels⟩
  · have h1' : kExpr ≠ kName := by decide
    have h2' : kExpr ≠ kLevel := by decide
    have h3' : kExpr ≠ kLevels := by decide
    simp only [h1', h2', h3', ↓reduceIte] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
      cases hv
      obtain ⟨hst, n, hn, hd⟩ := exprNode_run hok hpk hsub h1
      have hg := hm.ext hst.ext
      refine ⟨hst, ⟨hg.names, hg.levels, hg.lists,
        getElem?_insert_good hg.exprs ⟨n, by rw [exprAt]; exact hn, hd⟩⟩, holds_exprs, keeps_exprs⟩
  · have h1' : kLevels ≠ kName := by decide
    have h2' : kLevels ≠ kLevel := by decide
    simp only [h1', h2', ↓reduceIte] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
      cases hv
      obtain ⟨hst, n, hn, hd⟩ := levelsNode_run hok hpk hsub h1
      have hg := hm.ext hst.ext
      refine ⟨hst, ⟨hg.names, hg.levels,
        getElem?_insert_good hg.lists ⟨n, by rw [levelsAt]; exact hn, hd⟩, hg.exprs⟩,
        holds_lists, keeps_lists⟩

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:189-223 sGo — **the sparse read keeps the
memo good and holds what it read**, with everything it held before. -/
theorem sparseGo_run {pk : OleanPins} {r : Region} {b : Frontier} :
    ∀ (g : Nat) {k : UInt8} {m m' : SM} {s s' : AState}, StateOK s → NullsRel s.store pk →
      IsKind k → SparseGood s.store r m → FrontierGood s.store r b →
      ConRon.Arena.Frontend.Olean.sGo pk r b k g m s = .ok (some m', s') →
      ParseStep s s' ∧ SparseGood s'.store r m' ∧ m'.holds b k g = true ∧ SMKeeps b m m' := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
  intro k m m' s s' hok hpk hk hm hb h
  -- the kid walk over the fields `fs` of the object at `g`
  have hkids : ∀ (fs : List (Nat × UInt8 × Bool)) {m m' : SM} {s s' : AState}, StateOK s →
      NullsRel s.store pk → (∀ f ∈ fs, IsKind f.2.1) → SparseGood s.store r m →
      FrontierGood s.store r b →
      ConRon.Arena.Frontend.Olean.kidsGo pk r b g fs m s = .ok (some m', s') →
      ParseStep s s' ∧ SparseGood s'.store r m' ∧ SMKeeps b m m' ∧
        ∀ i k' nil c, (i, k', nil) ∈ fs → ¬(nil = true ∧ r.fld g i = 1) →
          r.down g (r.fld g i) = some c → m'.holds b k' c = true := by
    intro fs
    induction fs with
    | nil =>
      intro m m' s s' hok _ _ hm _ h
      rw [ConRon.Arena.Frontend.Olean.kidsGo] at h
      obtain ⟨hv, rfl⟩ := AM.pure_ok h
      cases hv
      exact ⟨ParseStep.refl hok, hm, SMKeeps.refl _ _, fun _ _ _ _ hf => nomatch hf⟩
    | cons f fs ihf =>
      obtain ⟨i, k', nil⟩ := f
      intro m m' s s' hok hpk hks hm hb h
      have hk' : IsKind k' := hks _ List.mem_cons_self
      have hks' : ∀ f ∈ fs, IsKind f.2.1 := fun f hf => hks f (List.mem_cons_of_mem _ hf)
      generalize hF : ConRon.Arena.Frontend.Olean.kidsGo pk r b g ((i, k', nil) :: fs) m = f at h
      rw [ConRon.Arena.Frontend.Olean.kidsGo] at hF
      by_cases hn : (nil && r.fld g i == 1) = true
      · rw [ite_eq_left hn] at hF
        subst hF
        obtain ⟨hst, hg, hkp, hall⟩ := ihf hok hpk hks' hm hb h
        refine ⟨hst, hg, hkp, fun i' k'' nil' c hmem hnn hd => ?_⟩
        rcases List.mem_cons.mp hmem with he | hmem
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          simp only [Bool.and_eq_true, beq_iff_eq] at hn
          exact absurd hn hnn
        · exact hall i' k'' nil' c hmem hnn hd
      · rw [ite_eq_right hn] at hF
        split at hF
        · rename_i c hd
          subst hF
          obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
          cases o with
          | none => cases (AM.pure_ok h2).1
          | some m₁ =>
            obtain ⟨hst1, hg1, hh1, hkp1⟩ :=
              ih c (ConLeche.Frontend.Olean.Region.down_lt hd) hok hpk hk' hm hb h1
            obtain ⟨hst2, hg2, hkp2, hall⟩ := ihf hst1.ok (hpk.ext hst1.ext) hks' hg1
              (hb.ext hst1.ext) h2
            refine ⟨hst1.trans hst2, hg2, hkp1.trans hkp2, fun i' k'' nil' c' hmem hnn hd' => ?_⟩
            rcases List.mem_cons.mp hmem with he | hmem
            · simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, rfl, rfl⟩ := he
              rw [hd] at hd'
              cases hd'
              exact hkp2 _ _ hh1
            · exact hall i' k'' nil' c' hmem hnn hd'
        · subst hF
          cases (AM.pure_ok h).1
  generalize hF : ConRon.Arena.Frontend.Olean.sGo pk r b k g m = f at h
  rw [ConRon.Arena.Frontend.Olean.sGo] at hF
  by_cases hh : m.holds b k g = true
  · rw [ite_eq_left hh] at hF
    subst hF
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    exact ⟨ParseStep.refl hok, hm, hh, SMKeeps.refl _ _⟩
  · rw [ite_eq_right hh] at hF
    by_cases hf : r.fits g = true
    · rw [ite_eq_left hf] at hF
      split at hF
      · subst hF; cases (AM.pure_ok h).1
      · rename_i fs hfs
        subst hF
        obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
        cases o with
        | none => cases (AM.pure_ok h2).1
        | some m₁ =>
          obtain ⟨hst1, hg1, hkp1, hall⟩ := hkids fs hok hpk
            (fun f hf' => ConLeche.Frontend.Olean.kidTable_kinds hfs f hf') hm hb h1
          obtain ⟨hst2, hg2, hh2, hkp2⟩ := sparseBuildIn_run hst1.ok (hpk.ext hst1.ext) hk hg1
            (hb.ext hst1.ext) (fun k' c hkid => by
              obtain ⟨-, fs', hfs', i, nil, hmem, hnn, hd⟩ := hkid
              rw [hfs] at hfs'
              cases hfs'
              exact hall i k' nil c hmem hnn hd) h2
          exact ⟨hst1.trans hst2, hg2, hh2, hkp1.trans hkp2⟩
    · rw [ite_eq_right hf] at hF
      subst hF
      cases (AM.pure_ok h).1

/-- con-leche: ConLeche/Frontend/Olean/Sparse.lean:234-242 sparseNameP — **a name read sparsely
is the specification's** (`sparseNameP_eq`: upstream's sparse read is `nameP`). -/
theorem sparseNameP_run {pk : OleanPins} {r : Region} {v : UInt64} {s s' : AState}
    (hok : StateOK s) (hpk : NullsRel s.store pk) {x : NIdx}
    (h : ConRon.Arena.Frontend.Olean.sparseNameP pk r v s = .ok (some x, s')) :
    ParseStep s s' ∧ ∃ n, ConLeche.Frontend.Olean.nameP r v = some n ∧ denoteN s'.store.ns x = some n := by
  generalize hF : ConRon.Arena.Frontend.Olean.sparseNameP pk r v = f at h
  unfold ConRon.Arena.Frontend.Olean.sparseNameP at hF
  unfold ConLeche.Frontend.Olean.nameP
  by_cases hv : (v == 1) = true
  · rw [ite_eq_left hv] at hF
    subst hF
    simp only [hv, ↓reduceIte]
    obtain ⟨hx, rfl⟩ := AM.pure_ok h
    cases hx
    exact ⟨ParseStep.refl hok, _, rfl, hpk.anon⟩
  · rw [ite_eq_right hv] at hF
    simp only [hv, Bool.false_eq_true, ↓reduceIte]
    split at hF
    · rename_i c hc
      subst hF
      rw [hc]
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
      cases o with
      | none => cases (AM.pure_ok h2).1
      | some m =>
        obtain ⟨hx, rfl⟩ := AM.pure_ok h2
        obtain ⟨hst, hg, hh, -⟩ := sparseGo_run c hok hpk (Or.inl rfl) (SparseGood.empty _ _)
          (FrontierGood.empty _ _) h1
        obtain ⟨n, h3, h4⟩ := sparseLookup_good hg.names (FrontierGood.empty _ r).names hx.symm
        exact ⟨hst, n, h3, h4⟩
    · subst hF
      cases (AM.pure_ok h).1

end ConRon.Bridge.Frontend.Olean
