/-
# `ConRon.Bridge.Frontend.Olean.Value` — **Theorem 1 for a theorem's value, read in its job**

`readValue_run`: on the record `modelFs F` of a snapshot, where the twin's read of a theorem's
value answers, the handle it returns denotes the value upstream's `ValueAt` names at the
reference's code.  It rests on three things:

* the sparse decoder over a frontier (`sGo_run`, `frontierExpr_run`), upstream's `sGo_spec`
  over handles: the memo's handles denote the specification's values (`SMGood`), and so do the
  frontier's (`FrontierGood`, `Closure.lean`);
* the values' relation `ValuesRel` (`Records.lean`), which `readOleans_run` exports: each
  module's frontier is good on the region of its files on the snapshot;
* the worker's cache (`CacheOK`): a cached region is the region of the files of the module it
  is cached for.  It holds of `{}` and `readValue` keeps it.
-/
module

public import ConRon.Bridge.Frontend.Olean.Records

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins SM Frontier Sub ModRef ValueCache)
open ConLeche.Frontend.Olean (Region Kid kName kLevel kLevels kExpr kidTable nameAt levelAt
  levelsAt exprAt IsKind SearchPath)

/-! ## The context

A theorem's value is read inside its job's scratch bracket, so the context of the read does not
ask for the flag: the node runs of `Nodes.lean` hold either way. -/

/-- con-leche: none — what every run of the sparse decoder carries. -/
structure VCtx (pk : OleanPins) (s : AState) : Prop where
  ok : StateOK s
  nulls : NullsRel s.store pk

theorem VCtx.step {pk : OleanPins} {s s' : AState} (h : VCtx pk s) (hst : ParseStep s s') :
    VCtx pk s' :=
  ⟨hst.ok, h.nulls.ext hst.ext⟩

/-! ## The memo -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:33 SM.Good — every handle the memo
holds denotes the specification's value at its location. -/
@[expose] def SMGood (st : EStore) (r : Region) (sm : SM) : Prop :=
  (∀ c h, sm.names[c]? = some h → ∃ n, nameAt r c = some n ∧ denoteN st.ns h = some n) ∧
  (∀ c h, sm.levels[c]? = some h → ∃ u, levelAt r c = some u ∧ denoteL st.ls h = some u) ∧
  (∀ c h, sm.lists[c]? = some h → ∃ us, levelsAt r c = some us ∧ denoteLs st.lss h = some us) ∧
  (∀ c h, sm.exprs[c]? = some h → ∃ e, exprAt r c = some e ∧ denoteE st h = some e)

theorem SMGood.empty (st : EStore) (r : Region) : SMGood st r {} :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h,
   fun _ _ h => by simp at h⟩

theorem SMGood.ext {st st' : EStore} {r : Region} {sm : SM} (h : SMGood st r sm)
    (hx : Ext st st') : SMGood st' r sm :=
  ⟨fun c v hv => let ⟨n, a, b⟩ := h.1 c v hv; ⟨n, a, denoteN_ext b hx⟩,
   fun c v hv => let ⟨n, a, b⟩ := h.2.1 c v hv; ⟨n, a, denoteL_ext b hx⟩,
   fun c v hv => let ⟨n, a, b⟩ := h.2.2.1 c v hv; ⟨n, a, denoteLs_ext b hx⟩,
   fun c v hv => let ⟨n, a, b⟩ := h.2.2.2 c v hv; ⟨n, a, denote_ext b hx⟩⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:40 SM.Sub -/
@[expose] def SMSub (a b : SM) : Prop := ∀ k g, a.has k g = true → b.has k g = true

theorem SMSub.refl (a : SM) : SMSub a a := fun _ _ h => h

theorem SMSub.trans {a b c : SM} (h1 : SMSub a b) (h2 : SMSub b c) : SMSub a c :=
  fun k g h => h2 k g (h1 k g h)

theorem SMSub.holds {a c : SM} (h : SMSub a c) {b : Frontier} {k : UInt8} {g : Nat}
    (ha : a.holds b k g = true) : c.holds b k g = true := by
  simp only [SM.holds, Bool.or_eq_true] at ha ⊢
  exact ha.imp (h k g) id

theorem SM.has_name (sm : SM) (g : Nat) : sm.has kName g = sm.names.contains g := by
  simp [SM.has]
theorem SM.has_level (sm : SM) (g : Nat) : sm.has kLevel g = sm.levels.contains g := by
  simp [SM.has, kinds_ne'.1.symm]
theorem SM.has_levels (sm : SM) (g : Nat) : sm.has kLevels g = sm.lists.contains g := by
  simp [SM.has, kinds_ne'.2.2.1.symm, kinds_ne'.2.2.2.2.1.symm]
theorem SM.has_expr (sm : SM) (g : Nat) : sm.has kExpr g = sm.exprs.contains g := by
  simp [SM.has, kinds_ne'.2.1.symm, kinds_ne'.2.2.2.1.symm, kinds_ne'.2.2.2.2.2]

theorem Frontier.has_name (b : Frontier) (g : Nat) : b.has kName g = (b.names.get g).isSome := by
  simp [Frontier.has]
theorem Frontier.has_level (b : Frontier) (g : Nat) : b.has kLevel g = (b.levels.get g).isSome := by
  simp [Frontier.has, kinds_ne'.1.symm]
theorem Frontier.has_levels (b : Frontier) (g : Nat) : b.has kLevels g = (b.lists.get g).isSome := by
  simp [Frontier.has, kinds_ne'.2.2.1.symm, kinds_ne'.2.2.2.2.1.symm]
theorem Frontier.has_expr (b : Frontier) (g : Nat) : b.has kExpr g = (b.exprs.get g).isSome := by
  simp [Frontier.has, kinds_ne'.2.1.symm, kinds_ne'.2.2.2.1.symm, kinds_ne'.2.2.2.2.2]

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:116 lookup_eq — a kid the memo or the
frontier holds has a handle, and it satisfies what both promise. -/
theorem lookup_good {α : Type} {P : Nat → α → Prop} {m : Std.HashMap Nat α}
    {t : ConLeche.Frontend.Olean.Table α} (hm : ∀ c v, m[c]? = some v → P c v)
    (ht : TableRel P t) {c : Nat} (h : m.contains c = true ∨ (t.get c).isSome = true) :
    ∃ v, ConLeche.Frontend.Olean.lookup m t c = some v ∧ P c v := by
  unfold ConLeche.Frontend.Olean.lookup
  cases e : m[c]? with
  | some v => exact ⟨v, rfl, hm c v e⟩
  | none =>
    rcases h with h | h
    · rw [Std.HashMap.contains_eq_isSome_getElem?, e] at h; cases h
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
      exact ⟨v, hv, ht.get hv⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:142-154 SM.Good.name — the memo over
the frontier answers at every kid the read holds. -/
theorem subRel_of {st : EStore} {r : Region} {sm : SM} {b : Frontier} {k : UInt8} {g : Nat}
    (hG : SMGood st r sm) (hB : FrontierGood st r b)
    (hkids : ∀ k' c, Kid r k g k' c → sm.holds b k' c = true) :
    SubRel st r k g (sm.subIn b) (fun c _ => exprAt r c) (fun c _ => nameAt r c)
      (fun c _ => levelAt r c) (fun c _ => levelsAt r c) := by
  refine ⟨fun c _ hk => ?_, fun c _ hk => ?_, fun c _ hk => ?_, fun c _ hk => ?_⟩
  · have hh := hkids _ _ hk
    simp only [SM.holds, SM.has_name, Frontier.has_name, Bool.or_eq_true] at hh
    obtain ⟨x, hx, n, h1, h2⟩ := lookup_good hG.1 hB.names hh
    exact ⟨x, n, hx, h2, h1⟩
  · have hh := hkids _ _ hk
    simp only [SM.holds, SM.has_level, Frontier.has_level, Bool.or_eq_true] at hh
    obtain ⟨x, hx, n, h1, h2⟩ := lookup_good hG.2.1 hB.levels hh
    exact ⟨x, n, hx, h2, h1⟩
  · have hh := hkids _ _ hk
    simp only [SM.holds, SM.has_levels, Frontier.has_levels, Bool.or_eq_true] at hh
    obtain ⟨x, hx, n, h1, h2⟩ := lookup_good hG.2.2.1 hB.lists hh
    exact ⟨x, n, hx, h2, h1⟩
  · have hh := hkids _ _ hk
    simp only [SM.holds, SM.has_expr, Frontier.has_expr, Bool.or_eq_true] at hh
    obtain ⟨x, hx, n, h1, h2⟩ := lookup_good hG.2.2.2 hB.exprs hh
    exact ⟨x, n, hx, h2, h1⟩

/-- A map with one more entry keeps its entries' property. -/
theorem good_insert {α : Type} {P : Nat → α → Prop} {m : Std.HashMap Nat α}
    (hm : ∀ c v, m[c]? = some v → P c v) {g : Nat} {v : α} (hv : P g v) :
    ∀ c w, (m.insert g v)[c]? = some w → P c w := by
  intro c w h
  rw [Std.HashMap.getElem?_insert] at h
  by_cases e : g = c
  · subst e
    simp only [BEq.rfl, ite_true, Option.some.injEq] at h
    subst h
    exact hv
  · rw [beq_eq_false_iff_ne.mpr e] at h
    exact hm c w h

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:171 SM.build_spec — **the object at
`g`, read as kind `k` from kids the read holds**: the node function's run, its handle denoting
the specification's value, added to the memo. -/
theorem buildIn_run {pk : OleanPins} {r : Region} {b : Frontier} {k : UInt8} {g : Nat}
    {sm sm' : SM} {s s' : AState} (hk : IsKind k) (hctx : VCtx pk s) (hG : SMGood s.store r sm)
    (hB : FrontierGood s.store r b) (hkids : ∀ k' c, Kid r k g k' c → sm.holds b k' c = true)
    (h : ConRon.Arena.Frontend.Olean.SM.buildIn pk r b k g sm s = .ok (some sm', s')) :
    ParseStep s s' ∧ SMGood s'.store r sm' ∧ sm'.has k g = true ∧ SMSub sm sm' := by
  have hsub := subRel_of (k := k) hG hB hkids
  have sub_all : ∀ (sm2 : SM), (∀ k' c, sm.has k' c = true → sm2.has k' c = true) → SMSub sm sm2 :=
    fun _ h => h
  rcases hk with rfl | rfl | rfl | rfl
  · simp only [ConRon.Arena.Frontend.Olean.SM.buildIn, ite_true] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
    cases hv
    subst hs
    obtain ⟨hst, x, hx, hd⟩ := nameNode_run hctx.ok hctx.nulls hsub h1
    have hG' := hG.ext hst.ext
    refine ⟨hst, ⟨good_insert hG'.1 ⟨x, by rw [nameAt]; exact hx, hd⟩, hG'.2⟩,
      by rw [SM.has_name]; simp [Std.HashMap.contains_insert], sub_all _ ?_⟩
    intro k' c h; unfold ConRon.Arena.Frontend.Olean.SM.has at h ⊢
    repeat' split <;> simp_all [Std.HashMap.contains_insert]
  · simp only [ConRon.Arena.Frontend.Olean.SM.buildIn, kinds_ne'.1.symm, ite_false, ite_true] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
    cases hv
    subst hs
    obtain ⟨hst, x, hx, hd⟩ := levelNode_run hctx.ok hctx.nulls hsub h1
    have hG' := hG.ext hst.ext
    refine ⟨hst, ⟨hG'.1, good_insert hG'.2.1 ⟨x, by rw [levelAt]; exact hx, hd⟩, hG'.2.2⟩,
      by rw [SM.has_level]; simp [Std.HashMap.contains_insert], sub_all _ ?_⟩
    intro k' c h; unfold ConRon.Arena.Frontend.Olean.SM.has at h ⊢
    repeat' split <;> simp_all [Std.HashMap.contains_insert]
  · simp only [ConRon.Arena.Frontend.Olean.SM.buildIn, kinds_ne'.2.1.symm, kinds_ne'.2.2.2.1.symm,
      kinds_ne'.2.2.2.2.2, ite_false] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
    cases hv
    subst hs
    obtain ⟨hst, x, hx, hd⟩ := exprNode_run hctx.ok hctx.nulls hsub h1
    have hG' := hG.ext hst.ext
    refine ⟨hst, ⟨hG'.1, hG'.2.1, hG'.2.2.1,
      good_insert hG'.2.2.2 ⟨x, by rw [exprAt]; exact hx, hd⟩⟩,
      by rw [SM.has_expr]; simp [Std.HashMap.contains_insert], sub_all _ ?_⟩
    intro k' c h; unfold ConRon.Arena.Frontend.Olean.SM.has at h ⊢
    repeat' split <;> simp_all [Std.HashMap.contains_insert]
  · simp only [ConRon.Arena.Frontend.Olean.SM.buildIn, kinds_ne'.2.2.1.symm,
      kinds_ne'.2.2.2.2.1.symm, ite_false, ite_true] at h
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h2
    cases o with
    | none => cases hv
    | some v =>
    cases hv
    subst hs
    obtain ⟨hst, x, hx, hd⟩ := levelsNode_run hctx.ok hctx.nulls hsub h1
    have hG' := hG.ext hst.ext
    refine ⟨hst, ⟨hG'.1, hG'.2.1, good_insert hG'.2.2.1 ⟨x, by rw [levelsAt]; exact hx, hd⟩,
      hG'.2.2.2⟩, by rw [SM.has_levels]; simp [Std.HashMap.contains_insert], sub_all _ ?_⟩
    intro k' c h; unfold ConRon.Arena.Frontend.Olean.SM.has at h ⊢
    repeat' split <;> simp_all [Std.HashMap.contains_insert]

/-! ## The recursion -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:273 SGoSpec — what an answering `sGo`
gives: the memo holds the object, and every handle it holds denotes. -/
@[expose] def SGoRun (pk : OleanPins) (r : Region) (b : Frontier) (g : Nat) : Prop :=
  ∀ (k : UInt8) (sm sm' : SM) (s s' : AState), IsKind k → VCtx pk s → SMGood s.store r sm →
    FrontierGood s.store r b →
    ConRon.Arena.Frontend.Olean.sGo pk r b k g sm s = .ok (some sm', s') →
    ParseStep s s' ∧ SMGood s'.store r sm' ∧ sm'.holds b k g = true ∧ SMSub sm sm'

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:284 kidsGo_spec -/
theorem kidsGo_run {pk : OleanPins} {r : Region} {b : Frontier} {k : UInt8} {g : Nat}
    (ih : ∀ c, c < g → SGoRun pk r b c) {fs₀ : List (Nat × UInt8 × Bool)}
    (hfs : kidTable k (r.tag g) (r.nobjs g) = some fs₀) :
    ∀ (fs : List (Nat × UInt8 × Bool)) (sm sm' : SM) (s s' : AState), (∀ f ∈ fs, f ∈ fs₀) →
      VCtx pk s → SMGood s.store r sm → FrontierGood s.store r b →
      ConRon.Arena.Frontend.Olean.kidsGo pk r b g fs sm s = .ok (some sm', s') →
      ParseStep s s' ∧ SMGood s'.store r sm' ∧ SMSub sm sm' ∧
        ∀ f ∈ fs, ∀ c, ¬ (f.2.2 = true ∧ r.fld g f.1 = 1) → r.down g (r.fld g f.1) = some c →
          sm'.holds b f.2.1 c = true
  | [], sm, sm', s, s', _, hctx, hG, _, h => by
    rw [ConRon.Arena.Frontend.Olean.kidsGo] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hctx.ok, hG, SMSub.refl _, fun _ hf => by simp at hf⟩
  | (i, k', nil) :: fs, sm, sm', s, s', hsub, hctx, hG, hB, h => by
    have hmem : (i, k', nil) ∈ fs₀ := hsub _ (by simp)
    have hsub' : ∀ f ∈ fs, f ∈ fs₀ := fun f hf => hsub f (by simp [hf])
    have hk' : IsKind k' := ConLeche.Frontend.Olean.kidTable_kinds hfs _ hmem
    generalize hK : ConRon.Arena.Frontend.Olean.kidsGo pk r b g ((i, k', nil) :: fs) sm = fn at h
    rw [ConRon.Arena.Frontend.Olean.kidsGo] at hK
    by_cases hnil : (nil && r.fld g i == 1) = true
    · rw [ite_eq_left hnil] at hK
      subst hK
      obtain ⟨hst, hG', hS, hall⟩ := kidsGo_run ih hfs fs sm sm' s s' hsub' hctx hG hB h
      refine ⟨hst, hG', hS, fun f hf c hne hd => ?_⟩
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · simp only [Bool.and_eq_true, beq_iff_eq] at hnil
        exact absurd ⟨hnil.1, hnil.2⟩ hne
      · exact hall f hf c hne hd
    · rw [ite_eq_right hnil] at hK
      split at hK
      · rename_i c hd
        subst hK
        have hlt : c < g := ConLeche.Frontend.Olean.Region.down_lt hd
        obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
        cases o with
        | none => cases (AM.pure_ok h2).1
        | some sm1 =>
        obtain ⟨hst1, hG1, hh1, hS1⟩ := ih c hlt k' sm sm1 s s₁ hk' hctx hG hB h1
        obtain ⟨hst2, hG', hS', hall⟩ := kidsGo_run ih hfs fs sm1 sm' s₁ s' hsub' (hctx.step hst1)
          hG1 (hB.ext hst1.ext) h2
        refine ⟨hst1.trans hst2, hG', hS1.trans hS', fun f hf c' hne hd' => ?_⟩
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · rw [hd] at hd'; cases hd'; exact hS'.holds hh1
        · exact hall f hf c' hne hd'
      · subst hK
        cases (AM.pure_ok h).1

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:341 sGo_spec — **the sparse decoder
over a frontier**: where it answers, the memo holds the object and denotes the specification's
values. -/
theorem sGo_run (pk : OleanPins) (r : Region) (b : Frontier) : ∀ g, SGoRun pk r b g := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
  intro k sm sm' s s' hk hctx hG hB h
  generalize hK : ConRon.Arena.Frontend.Olean.sGo pk r b k g sm = fn at h
  rw [ConRon.Arena.Frontend.Olean.sGo] at hK
  by_cases hh : sm.holds b k g = true
  · rw [ite_eq_left hh] at hK
    subst hK
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hctx.ok, hG, hh, SMSub.refl _⟩
  · rw [ite_eq_right hh] at hK
    by_cases hfit : r.fits g = true
    · rw [ite_eq_left hfit] at hK
      split at hK
      · subst hK
        cases (AM.pure_ok h).1
      · rename_i fs hfs
        subst hK
        obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
        cases o with
        | none => cases (AM.pure_ok h2).1
        | some sm1 =>
        obtain ⟨hst1, hG1, hS1, hall⟩ :=
          kidsGo_run ih hfs fs sm sm1 s s₁ (fun f hf => hf) hctx hG hB h1
        have hkids : ∀ k' c, Kid r k g k' c → sm1.holds b k' c = true := by
          intro k' c ⟨_, fs', hfs', i, nil, hm, hne, hd⟩
          rw [hfs] at hfs'; cases hfs'
          exact hall (i, k', nil) hm c hne hd
        obtain ⟨hst2, hG', hh', hS'⟩ :=
          buildIn_run hk (hctx.step hst1) hG1 (hB.ext hst1.ext) hkids h2
        refine ⟨hst1.trans hst2, hG', ?_, hS1.trans hS'⟩
        simp only [SM.holds, hh', Bool.true_or]
    · rw [ite_eq_right hfit] at hK
      subst hK
      cases (AM.pure_ok h).1

/-- con-leche: ConLeche/Verify/Frontend/Olean/Sparse.lean:385 frontierExpr_eq — **the `Expr` at
location `c`, read over a good frontier**, denotes the specification's. -/
theorem frontierExpr_run {pk : OleanPins} {r : Region} {b : Frontier} {c : Nat} {e : EIdx}
    {s s' : AState} (hctx : VCtx pk s) (hB : FrontierGood s.store r b)
    (h : ConRon.Arena.Frontend.Olean.frontierExpr pk r b c s = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ x, exprAt r c = some x ∧ denoteE s'.store e = some x := by
  unfold ConRon.Arena.Frontend.Olean.frontierExpr at h
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
  cases o with
  | none => cases (AM.pure_ok h2).1
  | some sm =>
  obtain ⟨hv, hs⟩ := AM.pure_ok h2
  subst hs
  have hK : IsKind kExpr := Or.inr (Or.inr (Or.inl rfl))
  obtain ⟨hst, hG, hh, -⟩ := sGo_run pk r b c kExpr {} sm s s' hK hctx (SMGood.empty _ r) hB h1
  simp only [SM.holds, SM.has_expr, Frontier.has_expr, Bool.or_eq_true] at hh
  obtain ⟨v, hv', x, h3, h4⟩ := lookup_good hG.2.2.2 (hB.ext hst.ext).exprs hh
  rw [hv'] at hv
  cases hv
  exact ⟨hst, x, h3, h4⟩

end ConRon.Bridge.Frontend.Olean
