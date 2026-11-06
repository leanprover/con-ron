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
import ConRon.Bridge.Checker.Pins

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

/-! ## The worker's cache -/

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:126-131 ValueCache — **a cached region is the
region of the files of the module it is cached for**, by upstream's values. -/
@[expose] def CacheOK (sp : SearchPath) (F : FS) (valuesP : Array ConLeche.Frontend.Olean.ModRef)
    (c : ValueCache) : Prop :=
  ∀ r, c.region = some r → ∃ mdP f a, valuesP[c.idx]? = some mdP ∧
    (ConLeche.Frontend.Olean.readFiles sp mdP.name .private : ModelIO _) F (.ok (.ok f)) ∧
    f.viewRegion .private = some (r, a)

theorem CacheOK.empty (sp : SearchPath) (F : FS) (valuesP : Array ConLeche.Frontend.Olean.ModRef) :
    CacheOK sp F valuesP {} := fun r h => by cases h

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:133-148 regionFor — the read of a module's
region off its files: the files are the snapshot's, and the cache it leaves is good. -/
theorem readRegion_run {F : FS} {pk : OleanPins} {sp : SearchPath} {m : NIdx} {idx : Nat}
    {valuesP : Array ConLeche.Frontend.Olean.ModRef} {mdP : ConLeche.Frontend.Olean.ModRef}
    {c' : ValueCache} {r : Region} {s s' : AState} (hm : denoteN s.store.ns m = some mdP.name)
    (hidx : valuesP[idx]? = some mdP)
    (h : ConRon.Arena.Frontend.Olean.regionFor.readRegion (modelFs F) pk sp m idx s =
      .ok ((c', .ok r), s')) :
    s' = s ∧ CacheOK sp F valuesP c' ∧ ∃ f a,
      (ConLeche.Frontend.Olean.readFiles sp mdP.name .private : ModelIO _) F (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) := by
  unfold ConRon.Arena.Frontend.Olean.regionFor.readRegion at h
  obtain ⟨mn, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, hd1⟩ := readName_run h1
  obtain rfl : mn = mdP.name := Option.some.inj (hd1.symm.trans hm)
  cases hrf : ConRon.Arena.Frontend.Olean.readFiles (modelFs F) sp mdP.name .private with
  | error e =>
    rw [hrf] at h2
    cases (AM.pure_ok h2).1
  | ok f =>
  rw [hrf] at h2
  simp only [] at h2
  cases hv : f.viewRegion .private with
  | none =>
    rw [hv] at h2
    obtain ⟨_, s₂, -, h3⟩ := AM.bind_ok h2
    cases (AM.pure_ok h3).1
  | some p =>
  obtain ⟨r0, a0⟩ := p
  rw [hv] at h2
  obtain ⟨hv', rfl⟩ := AM.pure_ok h2
  simp only [Prod.mk.injEq, Except.ok.injEq] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  refine ⟨rfl, fun r' hr' => ?_, f, a0, readFiles_sim hrf, hv⟩
  simp only [Option.some.injEq] at hr'
  subst hr'
  exact ⟨mdP, f, a0, hidx, readFiles_sim hrf, hv⟩

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:133-148 regionFor — **the region of module
`idx`, from the cache or the files**: the files of the module upstream's values name at `idx`. -/
theorem regionFor_run {F : FS} {pk : OleanPins} {sp : SearchPath} {m : NIdx} {idx : Nat}
    {valuesP : Array ConLeche.Frontend.Olean.ModRef} {mdP : ConLeche.Frontend.Olean.ModRef}
    {c c' : ValueCache} {r : Region} {s s' : AState} (hm : denoteN s.store.ns m = some mdP.name)
    (hidx : valuesP[idx]? = some mdP) (hc : CacheOK sp F valuesP c)
    (h : ConRon.Arena.Frontend.Olean.regionFor (modelFs F) pk sp m idx c s = .ok ((c', .ok r), s')) :
    s' = s ∧ CacheOK sp F valuesP c' ∧ ∃ f a,
      (ConLeche.Frontend.Olean.readFiles sp mdP.name .private : ModelIO _) F (.ok (.ok f)) ∧
      f.viewRegion .private = some (r, a) := by
  unfold ConRon.Arena.Frontend.Olean.regionFor at h
  cases hr : c.region with
  | none =>
    rw [hr] at h
    exact readRegion_run hm hidx h
  | some r0 =>
    rw [hr] at h
    simp only [] at h
    by_cases hi : (c.idx == idx) = true
    · rw [ite_eq_left hi] at h
      obtain ⟨hv, rfl⟩ := AM.pure_ok h
      simp only [Prod.mk.injEq, Except.ok.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨mdP', f, a, h1, h2, h3⟩ := hc _ hr
      rw [beq_iff_eq.mp hi, hidx] at h1
      cases h1
      exact ⟨rfl, hc, f, a, h2, h3⟩
    · rw [ite_eq_right hi] at h
      exact readRegion_run hm hidx h

/-! ## A theorem's value -/

theorem array_listRel_getElem? {α β : Type} {R : α → β → Prop} {a : Array α} {b : Array β}
    (h : ListRel R a.toList b.toList) {i : Nat} {x : α} (hx : a[i]? = some x) :
    ∃ y, b[i]? = some y ∧ R x y := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hx
  obtain ⟨hj, hr⟩ := listRel_get h (i := i) (by simpa using hi)
  refine ⟨b[i]'(by simpa using hj), Array.getElem?_eq_getElem _, ?_⟩
  simpa using hr

/-- con-leche: ConLeche/Frontend/Olean/Records.lean:150-162 readValue — **THEOREM 1 FOR A
THEOREM'S VALUE**: where the twin's read of the value at a reference's code answers, on the
record `modelFs F` of a snapshot, its handle denotes the value upstream's `ValueAt` names, on
upstream's values `valuesP` (`readOleans_run`'s); the state moves as a parse step does, whatever
the scratch flag, and the cache stays good. -/
theorem readValue_run {F : FS} {pk : OleanPins} {sp : SearchPath}
    {values : Array ModRef} {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    {c c' : ValueCache} {code : Nat} {e : EIdx} {s s' : AState}
    (hok : StateOK s) (hnu : NullsRel s.store pk) (hv : ValuesRel sp F s.store values valuesP)
    (hc : CacheOK sp F valuesP c)
    (h : ConRon.Arena.Frontend.Olean.readValue (modelFs F) pk sp values c code s =
      .ok ((c', .ok e), s')) :
    ParseStep s s' ∧ CacheOK sp F valuesP c' ∧
      ∃ x, denoteE s'.store e = some x ∧ ConLeche.Frontend.Olean.ValueAt sp F valuesP code x := by
  unfold ConRon.Arena.Frontend.Olean.readValue at h
  cases hmd : values[ConLeche.Frontend.Olean.refModule code]? with
  | none =>
    rw [hmd] at h
    cases (AM.pure_ok h).1
  | some md =>
  rw [hmd] at h
  simp only [] at h
  obtain ⟨mdP, hmdP, hname, f, hf, r0, a0, hreg0, hgood⟩ := array_listRel_getElem? hv hmd
  obtain ⟨p, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨c1, _ | r⟩ := p
  · cases (AM.pure_ok h2).1
  obtain ⟨rfl, hc1, f', a, hf', hreg⟩ := regionFor_run hname hmdP hc h1
  obtain rfl := ConLeche.Frontend.Olean.readFiles_unique hf hf'
  rw [hreg0] at hreg
  cases hreg
  simp only [] at h2
  obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
  cases o with
  | none =>
    obtain ⟨_, s₃, -, h5⟩ := AM.bind_ok h4
    cases (AM.pure_ok h5).1
  | some e' =>
  obtain ⟨hv', rfl⟩ := AM.pure_ok h4
  simp only [Prod.mk.injEq, Except.ok.injEq] at hv'
  obtain ⟨rfl, rfl⟩ := hv'
  obtain ⟨hst, x, hx, hdx⟩ := frontierExpr_run ⟨hok, hnu⟩ hgood h3
  exact ⟨hst, hc1, x, hdx, mdP, f, _, _, hmdP, hf, hreg0, hx⟩

/-! ## On a worker's store

A job runs on a worker's state, whose store is a persistent extension (`PExt`) of the driver's
state where the read ran with the scratch tier closed.  Everything the read hands the job is a
handle that denotes on that closed store, hence persistent, so `PExt` carries it. -/

/-- con-leche: none — a frontier good on a closed store is good on a persistent extension. -/
theorem FrontierGood.pmono {st st' : EStore} {r : Region} {b : Frontier} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) (h : FrontierGood st r b) (hx : PExt st st') :
    FrontierGood st' r b :=
  ⟨h.names.mono fun _ _ ⟨n, a, d⟩ => ⟨n, a, hx.lss.ls.ns _ _ (PersN_of_denote hwf hoff d) d⟩,
   h.levels.mono fun _ _ ⟨n, a, d⟩ => ⟨n, a, hx.lss.ls.lvl _ _ (PersL_of_denote hwf hoff d) d⟩,
   h.lists.mono fun _ _ ⟨n, a, d⟩ => ⟨n, a, hx.lss.lst _ _ (PersLs_of_denote hwf hoff d) d⟩,
   h.exprs.mono fun _ _ ⟨n, a, d⟩ => ⟨n, a, hx.expr _ _ (PersE_of_denote hwf hoff d) d⟩⟩

/-- con-leche: none — `ValuesRel` on a worker's store: the names and the frontiers' handles
denote on the closed store of the read, so they are persistent. -/
theorem ValuesRel.pmono {sp : SearchPath} {F : FS} {st st' : EStore}
    {values : Array ModRef} {valuesP : Array ConLeche.Frontend.Olean.ModRef}
    (hwf : StoreWF st) (hoff : st.scratchOn = false) (h : ValuesRel sp F st values valuesP)
    (hx : PExt st st') : ValuesRel sp F st' values valuesP :=
  ListRel.mono' (fun _ _ ⟨a, f, b, r, a', hr, hg⟩ =>
    ⟨hx.lss.ls.ns _ _ (PersN_of_denote hwf hoff a) a, f, b, r, a', hr,
      hg.pmono hwf hoff hx⟩) h

/-- con-leche: none — the reader's three nullary handles, on a worker's store. -/
theorem NullsRel.pmono {st st' : EStore} {pk : OleanPins} (hwf : StoreWF st)
    (hoff : st.scratchOn = false) (h : NullsRel st pk) (hx : PExt st st') : NullsRel st' pk :=
  ⟨hx.lss.ls.ns _ _ (PersN_of_denote hwf hoff h.anon) h.anon,
   hx.lss.ls.lvl _ _ (PersL_of_denote hwf hoff h.zero) h.zero,
   hx.lss.lst _ _ (PersLs_of_denote hwf hoff h.nil) h.nil⟩

end ConRon.Bridge.Frontend.Olean
