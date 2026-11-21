/-
# `ConRon.Bridge.Modular.ReachMemo` — reads with a part's memo, Theorem 1 (task #166)

The reach reads a part's constants with one memo per part (`entryWith`, `stmtWith`,
`entriesWith`, `Arena/Frontend/Olean/Present.lean`).  A memo whose every handle denotes the
specification's value at its location (`SparseGood`) stays so under the twin's root reads
(`memoAdd_runR`, `memoRoots_runR`), and every read off it is the specification's
(`memoName_runR`, `memoExpr_runR`): so a constant read is `entryAt`'s, a statement read is the
skeleton's (`StmtSkel`).  Upstream's reads with a good memo answer the same
(`entryWith_complete`, `stmtWith_complete`, `entriesWith_complete`), over `memoName_eq`.
Run style, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.ReadsParts
public import ConLeche.Verify.Driver.ReachFrom
public import ConLeche.Verify.Frontend.Olean.Reads
import ConLeche.Verify.Frontend.Olean.Present

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConLeche.Frontend.Olean (Region CEntryF CKindF nameP exprP nameAt exprAt kName kExpr IsKind
  constSkel entryAt bind_some_left)

/-! ## A failed read changes nothing -/

theorem bindSome_none {α β : Type} {x : AM α} {g : α → β} {s s' : AState}
    (h : (do let a ← x; pure (some (g a)) : AM (Option β)) s = .ok (none, s')) : False := by
  obtain ⟨_, _, _, h2⟩ := AM.bind_ok h
  cases (AM.pure_ok h2).1

theorem natWord_ok {k : Nat} {i : Nat} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.natWord k s = .ok (i, s')) : i = k ∧ s' = s := by
  unfold ConRon.Arena.Frontend.Olean.natWord at h
  split at h
  · exact (AM.fail_ok h).elim
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok h; exact ⟨rfl, rfl⟩

/-- The outcomes a node read's arms have: none and the state kept, or an intern then `some`. -/
macro "node_none" : tactic => `(tactic| first
  | (subst_vars; exact (AM.pure_ok ‹_›).2)
  | (subst_vars; exact (bindSome_none ‹_›).elim)
  | (subst_vars; cases (AM.pure_ok ‹_›).1))

theorem nameTail_none {r : Region} {g t : Nat} {p : NIdx} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.nameTail r g t p s = .ok (none, s')) : s' = s := by
  generalize hF : ConRon.Arena.Frontend.Olean.nameTail r g t p = fn at h
  unfold ConRon.Arena.Frontend.Olean.nameTail at hF
  split at hF
  · split at hF <;> node_none
  · split at hF
    · node_none
    · subst hF
      obtain ⟨_, _, _, h2⟩ := AM.bind_ok h
      exact (bindSome_none h2).elim

theorem nameNode_none {pk : OleanPins} {r : Region} {g : Nat}
    {sub : ConRon.Arena.Frontend.Olean.Sub} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.nameNode pk r g sub s = .ok (none, s')) : s' = s := by
  generalize hF : ConRon.Arena.Frontend.Olean.nameNode pk r g sub = fn at h
  unfold ConRon.Arena.Frontend.Olean.nameNode at hF
  split at hF
  · dsimp only at hF
    split at hF
    · split at hF
      · node_none
      · subst hF; exact nameTail_none h
    · node_none
  · node_none

theorem levelNode_none {pk : OleanPins} {r : Region} {g : Nat}
    {sub : ConRon.Arena.Frontend.Olean.Sub} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.levelNode pk r g sub s = .ok (none, s')) : s' = s := by
  generalize hF : ConRon.Arena.Frontend.Olean.levelNode pk r g sub = fn at h
  unfold ConRon.Arena.Frontend.Olean.levelNode at hF
  split at hF
  · split at hF <;> (try split at hF) <;> node_none
  · node_none

theorem levelsNode_none {pk : OleanPins} {r : Region} {g : Nat}
    {sub : ConRon.Arena.Frontend.Olean.Sub} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.levelsNode pk r g sub s = .ok (none, s')) : s' = s := by
  generalize hF : ConRon.Arena.Frontend.Olean.levelsNode pk r g sub = fn at h
  unfold ConRon.Arena.Frontend.Olean.levelsNode at hF
  split at hF
  · split at hF
    · split at hF
      · subst hF
        unfold ConRon.Arena.Frontend.Olean.levelsCons at h
        obtain ⟨_, _, _, h2⟩ := AM.bind_ok h
        exact (bindSome_none h2).elim
      · node_none
    · node_none
  · node_none

theorem exprNode_none {pk : OleanPins} {r : Region} {g : Nat}
    {sub : ConRon.Arena.Frontend.Olean.Sub} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.exprNode pk r g sub s = .ok (none, s')) : s' = s := by
  generalize hF : ConRon.Arena.Frontend.Olean.exprNode pk r g sub = fn at h
  unfold ConRon.Arena.Frontend.Olean.exprNode at hF
  split at hF
  · split at hF <;> (try split at hF) <;> (try split at hF) <;>
      first
      | node_none
      | (subst hF
         obtain ⟨i, s₁, h1, h2⟩ := AM.bind_ok h
         obtain ⟨-, rfl⟩ := natWord_ok h1
         first
         | exact (bindSome_none h2).elim
         | rcases hx : ConRon.Arena.Frontend.Olean.exprIn r g (r.fld g 2) sub with _ | x
           · rw [hx] at h2; exact (AM.pure_ok h2).2
           · rw [hx] at h2; exact (bindSome_none h2).elim)
  · node_none

theorem buildIn_none {pk : OleanPins} {r : Region} {b : ConRon.Arena.Frontend.Olean.Frontier}
    {k : UInt8} {g : Nat} {m : SM} {s s' : AState}
    (h : ConRon.Arena.Frontend.Olean.SM.buildIn pk r b k g m s = .ok (none, s')) : s' = s := by
  unfold ConRon.Arena.Frontend.Olean.SM.buildIn at h
  by_cases h1 : k = kName
  · simp only [h1, ↓reduceIte] at h
    obtain ⟨o, s₁, h2, h3⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h3
    cases o with
    | none => exact nameNode_none h2
    | some _ => cases hv
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : k = ConLeche.Frontend.Olean.kLevel
    · simp only [h2, ↓reduceIte] at h
      obtain ⟨o, s₁, h3, h4⟩ := AM.bind_ok h
      obtain ⟨hv, rfl⟩ := AM.pure_ok h4
      cases o with
      | none => exact levelNode_none h3
      | some _ => cases hv
    · simp only [h2, ↓reduceIte] at h
      by_cases h3 : k = ConLeche.Frontend.Olean.kLevels
      · simp only [h3, ↓reduceIte] at h
        obtain ⟨o, s₁, h4, h5⟩ := AM.bind_ok h
        obtain ⟨hv, rfl⟩ := AM.pure_ok h5
        cases o with
        | none => exact levelsNode_none h4
        | some _ => cases hv
      · simp only [h3, ↓reduceIte] at h
        obtain ⟨o, s₁, h4, h5⟩ := AM.bind_ok h
        obtain ⟨hv, rfl⟩ := AM.pure_ok h5
        cases o with
        | none => exact exprNode_none h4
        | some _ => cases hv

/-- **A sparse read that fails is a parse step all the same**: what it built of the object's
kids before the failure is interned soundly. -/
theorem sGo_none {pk : OleanPins} {r : Region} {b : ConRon.Arena.Frontend.Olean.Frontier} :
    ∀ (g : Nat) {k : UInt8} {m : SM} {s s' : AState}, StateOK s → NullsRel s.store pk →
      IsKind k → SparseGood s.store r m → FrontierGood s.store r b →
      ConRon.Arena.Frontend.Olean.sGo pk r b k g m s = .ok (none, s') → ParseStep s s' := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
  intro k m s s' hok hpk hk hm hb h
  have hkids : ∀ (fs : List (Nat × UInt8 × Bool)) {m : SM} {s s' : AState} {o : Option SM},
      StateOK s → NullsRel s.store pk → (∀ f ∈ fs, IsKind f.2.1) → SparseGood s.store r m →
      FrontierGood s.store r b →
      ConRon.Arena.Frontend.Olean.kidsGo pk r b g fs m s = .ok (o, s') → ParseStep s s' := by
    intro fs
    induction fs with
    | nil =>
      intro m s s' o hok _ _ _ _ h
      rw [ConRon.Arena.Frontend.Olean.kidsGo] at h
      obtain ⟨-, rfl⟩ := AM.pure_ok h
      exact ParseStep.refl hok
    | cons f fs ihf =>
      obtain ⟨i, k', nil⟩ := f
      intro m s s' o hok hpk hks hm hb h
      have hk' : IsKind k' := hks _ List.mem_cons_self
      have hks' : ∀ f ∈ fs, IsKind f.2.1 := fun f hf => hks f (List.mem_cons_of_mem _ hf)
      generalize hF : ConRon.Arena.Frontend.Olean.kidsGo pk r b g ((i, k', nil) :: fs) m = f at h
      rw [ConRon.Arena.Frontend.Olean.kidsGo] at hF
      by_cases hn : (nil && r.fld g i == 1) = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at hF
        subst hF
        exact ihf hok hpk hks' hm hb h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at hF
        split at hF
        · rename_i c hd
          subst hF
          obtain ⟨o₁, s₁, h1, h2⟩ := AM.bind_ok h
          cases o₁ with
          | none =>
            obtain ⟨-, rfl⟩ := AM.pure_ok h2
            exact ih c (ConLeche.Frontend.Olean.Region.down_lt hd) hok hpk hk' hm hb h1
          | some m₁ =>
            obtain ⟨hst1, hg1, -, -⟩ := sparseGo_run c hok hpk hk' hm hb h1
            exact hst1.trans (ihf hst1.ok (hpk.ext hst1.ext) hks' hg1 (hb.ext hst1.ext) h2)
        · subst hF
          obtain ⟨-, rfl⟩ := AM.pure_ok h
          exact ParseStep.refl hok
  generalize hF : ConRon.Arena.Frontend.Olean.sGo pk r b k g m = f at h
  rw [ConRon.Arena.Frontend.Olean.sGo] at hF
  by_cases hh : m.holds b k g = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hh)] at hF
    subst hF
    cases (AM.pure_ok h).1
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hh)] at hF
    by_cases hf : r.fits g = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hf)] at hF
      split at hF
      · subst hF
        obtain ⟨-, rfl⟩ := AM.pure_ok h
        exact ParseStep.refl hok
      · rename_i fs hfs
        subst hF
        obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
        have hst1 := hkids fs hok hpk
          (fun f hf' => ConLeche.Frontend.Olean.kidTable_kinds hfs f hf') hm hb h1
        cases o with
        | none =>
          obtain ⟨-, rfl⟩ := AM.pure_ok h2
          exact hst1
        | some m₁ =>
          rw [buildIn_none h2]
          exact hst1
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)] at hF
      subst hF
      obtain ⟨-, rfl⟩ := AM.pure_ok h
      exact ParseStep.refl hok

/-! ## The memo's roots -/

theorem memoAdd_runR {pk : OleanPins} {r : Region} {k : UInt8} (hk : IsKind k) {m m' : SM}
    {v : UInt64} {s s' : AState} (hctx : Ctx pk s) (hm : SparseGood s.store r m)
    (h : ConRon.Arena.Frontend.Olean.memoAdd pk r k m v s = .ok (m', s')) :
    ParseStep s s' ∧ SparseGood s'.store r m' := by
  generalize hF : ConRon.Arena.Frontend.Olean.memoAdd pk r k m v = f at h
  unfold ConRon.Arena.Frontend.Olean.memoAdd at hF
  split at hF
  · rename_i c _
    subst hF
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨sGo_none c hctx.ok hctx.nulls hk hm (FrontierGood.empty _ _) h1, SparseGood.empty _ _⟩
    | some m₁ =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨hst, hg, -, -⟩ := sparseGo_run c hctx.ok hctx.nulls hk hm (FrontierGood.empty _ _) h1
      exact ⟨hst, hg⟩
  · subst hF
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, hm⟩

theorem memoAddAll_runR {pk : OleanPins} {r : Region} {k : UInt8} (hk : IsKind k) :
    ∀ (vs : List UInt64) {m m' : SM} {s s' : AState}, Ctx pk s → SparseGood s.store r m →
      ConRon.Arena.Frontend.Olean.memoAddAll pk r k m vs s = .ok (m', s') →
      ParseStep s s' ∧ SparseGood s'.store r m'
  | [], m, m', s, s', hctx, hm, h => by
    rw [ConRon.Arena.Frontend.Olean.memoAddAll] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, hm⟩
  | v :: vs, m, m', s, s', hctx, hm, h => by
    rw [ConRon.Arena.Frontend.Olean.memoAddAll] at h
    obtain ⟨m₁, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hst1, hg1⟩ := memoAdd_runR hk hctx hm h1
    obtain ⟨hst2, hg2⟩ := memoAddAll_runR hk vs (hctx.step hst1) hg1 h2
    exact ⟨hst1.trans hst2, hg2⟩

theorem memoRoots_runR {pk : OleanPins} {r : Region} {m m' : SM} {sk : CEntryF UInt64 UInt64}
    {s s' : AState} (hctx : Ctx pk s) (hm : SparseGood s.store r m)
    (h : ConRon.Arena.Frontend.Olean.memoRoots pk r m sk s = .ok (m', s')) :
    ParseStep s s' ∧ SparseGood s'.store r m' := by
  unfold ConRon.Arena.Frontend.Olean.memoRoots at h
  obtain ⟨m₁, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hst1, hg1⟩ := memoAddAll_runR (Or.inl rfl) _ hctx hm h1
  obtain ⟨hst2, hg2⟩ := memoAddAll_runR (Or.inr (Or.inr (Or.inl rfl))) _ (hctx.step hst1) hg1 h2
  exact ⟨hst1.trans hst2, hg2⟩

/-! ## Reads off the memo -/

theorem memoName_runR {pk : OleanPins} {r : Region} {m : SM} {v : UInt64} {x : NIdx}
    {s s' : AState} (hctx : Ctx pk s) (hm : SparseGood s.store r m)
    (h : ConRon.Arena.Frontend.Olean.memoName pk r m v s = .ok (some x, s')) :
    ParseStep s s' ∧ ∃ n, nameP r v = some n ∧ denoteN s'.store.ns x = some n := by
  generalize hF : ConRon.Arena.Frontend.Olean.memoName pk r m v = f at h
  unfold ConRon.Arena.Frontend.Olean.memoName at hF
  by_cases hv : (v == 1) = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at hF
    subst hF
    obtain ⟨hx, rfl⟩ := AM.pure_ok h
    cases hx
    exact ⟨ParseStep.refl hctx.ok, .anonymous, by simp [nameP, hv], hctx.nulls.anon⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at hF
    split at hF
    · rename_i c hc
      split at hF
      · rename_i n hn
        subst hF
        obtain ⟨hx, rfl⟩ := AM.pure_ok h
        cases hx
        obtain ⟨z, hz, hd⟩ := hm.names c x hn
        refine ⟨ParseStep.refl hctx.ok, z, ?_, hd⟩
        simp only [nameP, hv, Bool.false_eq_true, ↓reduceIte, hc]
        exact hz
      · subst hF
        exact sparseNameP_run hctx.ok hctx.nulls h
    · subst hF
      cases (AM.pure_ok h).1

theorem frontierExpr_runR {pk : OleanPins} {r : Region} {c : Nat} {e : EIdx} {s s' : AState}
    (hctx : Ctx pk s)
    (h : ConRon.Arena.Frontend.Olean.frontierExpr pk r {} c s = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ x, exprAt r c = some x ∧ denoteE s'.store e = some x := by
  unfold ConRon.Arena.Frontend.Olean.frontierExpr at h
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
  cases o with
  | none => cases (AM.pure_ok h2).1
  | some sm =>
  obtain ⟨hv, rfl⟩ := AM.pure_ok h2
  obtain ⟨hst, hG, -, -⟩ := sparseGo_run c hctx.ok hctx.nulls (Or.inr (Or.inr (Or.inl rfl)))
    (SparseGood.empty _ r) (FrontierGood.empty _ _) h1
  exact ⟨hst, sparseLookup_good hG.exprs (FrontierGood.empty _ r).exprs hv.symm⟩

theorem memoExpr_runR {pk : OleanPins} {r : Region} {m : SM} {v : UInt64} {x : EIdx}
    {s s' : AState} (hctx : Ctx pk s) (hm : SparseGood s.store r m)
    (h : ConRon.Arena.Frontend.Olean.memoExpr pk r m v s = .ok (some x, s')) :
    ParseStep s s' ∧ ∃ e, exprP r v = some e ∧ denoteE s'.store x = some e := by
  generalize hF : ConRon.Arena.Frontend.Olean.memoExpr pk r m v = f at h
  unfold ConRon.Arena.Frontend.Olean.memoExpr at hF
  split at hF
  · rename_i c hc
    split at hF
    · rename_i e he
      subst hF
      obtain ⟨hx, rfl⟩ := AM.pure_ok h
      cases hx
      obtain ⟨z, hz, hd⟩ := hm.exprs c x he
      exact ⟨ParseStep.refl hctx.ok, z, by simp only [exprP, hc]; exact hz, hd⟩
    · subst hF
      unfold ConRon.Arena.Frontend.Olean.sparseExprP at h
      rw [hc] at h
      obtain ⟨hst, z, hz, hd⟩ := frontierExpr_runR hctx h
      exact ⟨hst, z, by simp only [exprP, hc]; exact hz, hd⟩
  · subst hF
    cases (AM.pure_ok h).1

/-! ## A constant's every pointer, read with effects -/

theorem optT_list_runX {α β γ : Type} {pk : OleanPins} {s₀ : AState} {den : EStore → β → Option γ}
    {f : α → OptionT AM β} {g : α → Option γ}
    (hden : ∀ {st st' : EStore} {y : β} {z : γ}, Ext st st' → den st y = some z → den st' y = some z)
    (hstep : ∀ a s s' y, Ctx pk s → Ext s₀.store s.store → f a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, g a = some z ∧ den s'.store y = some z) :
    ∀ (l : List α) {ys : List β} {s s' : AState}, Ctx pk s → Ext s₀.store s.store →
      l.mapM f s = .ok (some ys, s') →
      ParseStep s s' ∧ ∃ zs, l.mapM g = some zs ∧ ys.mapM (den s'.store) = some zs := by
  intro l
  induction l with
  | nil =>
    intro ys s s' hctx _ h
    simp only [List.mapM_nil] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    exact ⟨ParseStep.refl hctx.ok, [], rfl, rfl⟩
  | cons x l ih =>
    intro ys s s' hctx hx0 h
    simp only [List.mapM_cons] at h
    obtain ⟨y, s₁, h1, h⟩ := OT.bind_ok h
    obtain ⟨ys', s₂, h2, h⟩ := OT.bind_ok h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    subst hs
    obtain ⟨hst1, z, hz, hd⟩ := hstep x s s₁ y hctx hx0 h1
    obtain ⟨hst2, zs, hzs, hds⟩ := ih (hctx.step hst1) (hx0.trans hst1.ext) h2
    refine ⟨hst1.trans hst2, z :: zs, ?_, ?_⟩
    · simp only [List.mapM_cons, hz, hzs]; rfl
    · simp only [List.mapM_cons, hden hst2.ext hd, hds]; rfl

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:275-296 CKindF.mapM — a kind read pointer by
pointer, with effects, upstream's. -/
theorem kindMapT_run {pk : OleanPins} {s₀ : AState} {fn : UInt64 → AM (Option NIdx)}
    {fe : UInt64 → AM (Option EIdx)} {gn : UInt64 → Option ConLeche.Name} {ge : UInt64 → Option Expr}
    (hn : ∀ a s s' y, Ctx pk s → Ext s₀.store s.store → fn a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (he : ∀ a s s' y, Ctx pk s → Ext s₀.store s.store → fe a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, ge a = some z ∧ denoteE s'.store y = some z)
    (kind : CKindF UInt64 UInt64) {k : CKindF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s)
    (hx0 : Ext s₀.store s.store)
    (h : (kind.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) (fun v => OptionT.mk (fe v))) s
      = .ok (some k, s')) :
    ParseStep s s' ∧ ∃ kC, kind.mapM gn ge = some kC ∧
      k.mapM (denoteN s'.store.ns) (denoteE s'.store) = some kC := by
  have hdN : ∀ {st st' : EStore} {y : NIdx} {z : ConLeche.Name}, Ext st st' →
      denoteN st.ns y = some z → denoteN st'.ns y = some z := fun hx hy => denoteN_ext hy hx
  have hlist := fun (l : List UInt64) {ys : List NIdx} {s s' : AState} (hc : Ctx pk s)
      (hx : Ext s₀.store s.store)
      (h : l.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) s = .ok (some ys, s')) =>
    optT_list_runX (den := fun st => denoteN st.ns) (g := gn) hdN
      (fun a s s' y hc hx h => hn a s s' y hc hx h) l hc hx h
  cases kind with
  | ax u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | quot u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | defn v hh sf =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := he v s _ a hctx hx0 h1
    exact ⟨hst, .defn z hh sf, by simp [CKindF.mapM, hz, bind, Option.bind, pure],
      by simp [CKindF.mapM, hd, bind, Option.bind, pure]⟩
  | opaq v u =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := he v s _ a hctx hx0 h1
    exact ⟨hst, .opaq z u, by simp [CKindF.mapM, hz, bind, Option.bind, pure],
      by simp [CKindF.mapM, hd, bind, Option.bind, pure]⟩
  | thm v all =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨ns, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, z, hz, hd⟩ := he v s _ a hctx hx0 h1
    obtain ⟨hst2, zs, hzs, hds⟩ := hlist all (hctx.step hst1) (hx0.trans hst1.ext) h3
    refine ⟨hst1.trans hst2, .thm z zs, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hzs, bind, Option.bind, pure]
    · simp [CKindF.mapM, denote_ext hd hst2.ext, hds, bind, Option.bind, pure]
  | induct np ni all cs nn ir iu irf =>
    simp only [CKindF.mapM] at h
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨bs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := hlist all hctx hx0 h1
    obtain ⟨hst2, ws, hw, hdw⟩ := hlist cs (hctx.step hst1) (hx0.trans hst1.ext) h3
    refine ⟨hst1.trans hst2, .induct np ni zs ws nn ir iu irf, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hw, bind, Option.bind, pure]
    · simp [CKindF.mapM, mapM_denoteN_ext hst2.ext hd, hdw, bind, Option.bind, pure]
  | ctor ind ci np nf iu =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := hn ind s _ a hctx hx0 h1
    exact ⟨hst, .ctor z ci np nf iu, by simp [CKindF.mapM, hz, bind, Option.bind, pure],
      by simp [CKindF.mapM, hd, bind, Option.bind, pure]⟩
  | recur all np ni nmo nmi rules kk iu =>
    rw [recur_mapM] at h ⊢
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := hlist all hctx hx0 h1
    obtain ⟨hst2, ws, hw, hdw⟩ := optT_list_runX (pk := pk) (s₀ := s₀)
      (den := fun st (x : NIdx × Nat × EIdx) => do
        let c ← denoteN st.ns x.1
        let e ← denoteE st x.2.2
        pure (c, x.2.1, e))
      (g := fun (x : UInt64 × Nat × UInt64) => do
        let c ← gn x.1
        let e ← ge x.2.2
        pure (c, x.2.1, e))
      (fun {st st' y z} hx hy => by
        cases hn' : denoteN st.ns y.1 with
        | none => simp [hn'] at hy
        | some n =>
          cases he' : denoteE st y.2.2 with
          | none => simp [hn', he'] at hy
          | some e =>
            simp only [hn', he'] at hy
            simp only [denoteN_ext hn' hx, denote_ext he' hx]
            exact hy)
      (fun x s s' y hc hx hrun => by
        obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok hrun
        obtain ⟨b, s₂, h3, h4⟩ := OT.bind_ok h2
        obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
        obtain ⟨hst1, z, hz, hd⟩ := hn x.1 s _ a hc hx h1
        obtain ⟨hst2, w, hw, hdw⟩ := he x.2.2 s₁ _ b (hc.step hst1) (hx.trans hst1.ext) h3
        exact ⟨hst1.trans hst2, (z, x.2.1, w), by simp [hz, hw],
          by simp [denoteN_ext hd hst2.ext, hdw]⟩) rules (hctx.step hst1) (hx0.trans hst1.ext) h3
    refine ⟨hst1.trans hst2, .recur zs np ni nmo nmi ws kk iu, ?_, ?_⟩
    · rw [hz, hw]; rfl
    · rw [recur_mapM, mapM_denoteN_ext hst2.ext hd, hdw]; rfl

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM — **a constant read
pointer by pointer, with effects**, each name and expression upstream's: the constant is
upstream's, read back. -/
theorem entryMapT_run {pk : OleanPins} {s₀ : AState} {fn : UInt64 → AM (Option NIdx)}
    {fe : UInt64 → AM (Option EIdx)} {gn : UInt64 → Option ConLeche.Name} {ge : UInt64 → Option Expr}
    (hn : ∀ a s s' y, Ctx pk s → Ext s₀.store s.store → fn a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (he : ∀ a s s' y, Ctx pk s → Ext s₀.store s.store → fe a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, ge a = some z ∧ denoteE s'.store y = some z)
    (c : CEntryF UInt64 UInt64) {e : CEntryF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s)
    (hx0 : Ext s₀.store s.store)
    (h : (c.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) (fun v => OptionT.mk (fe v))) s
      = .ok (some e, s')) :
    ParseStep s s' ∧ ∃ eC, c.mapM gn ge = some eC ∧ denoteEntry s'.store e = some eC := by
  have hdN : ∀ {st st' : EStore} {y : NIdx} {z : ConLeche.Name}, Ext st st' →
      denoteN st.ns y = some z → denoteN st'.ns y = some z := fun hx hy => denoteN_ext hy hx
  rcases c with ⟨name, lps, type, kind⟩
  simp only [CEntryF.mapM] at h
  obtain ⟨n, s₁, h1, h⟩ := OT.bind_ok h
  obtain ⟨ls, s₂, h2, h⟩ := OT.bind_ok h
  obtain ⟨t, s₃, h3, h⟩ := OT.bind_ok h
  obtain ⟨k, s₄, h4, h⟩ := OT.bind_ok h
  obtain ⟨rfl, rfl⟩ := OT.pure_ok h
  obtain ⟨hst1, zn, hzn, hdn⟩ := hn name s s₁ n hctx hx0 h1
  have hc1 := hctx.step hst1
  obtain ⟨hst2, zl, hzl, hdl⟩ := optT_list_runX (den := fun st => denoteN st.ns) (g := gn) hdN
    (fun a s s' y hc hx h => hn a s s' y hc hx h) lps hc1 (hx0.trans hst1.ext) h2
  have hc2 := hc1.step hst2
  obtain ⟨hst3, zt, hzt, hdt⟩ := he type s₂ s₃ t hc2 ((hx0.trans hst1.ext).trans hst2.ext) h3
  have hc3 := hc2.step hst3
  have hx3 := ((hx0.trans hst1.ext).trans hst2.ext).trans hst3.ext
  obtain ⟨hst4, zk, hzk, hdk⟩ := kindMapT_run hn he kind hc3 hx3 h4
  refine ⟨((hst1.trans hst2).trans hst3).trans hst4, ⟨zn, zl, zt, zk⟩, ?_, ?_⟩
  · simp [CEntryF.mapM, hzn, hzl, hzt, hzk, bind, Option.bind, pure]
  · have e1 := denoteN_ext hdn ((hst2.trans hst3).trans hst4).ext
    have e2 := mapM_denoteN_ext (hst3.trans hst4).ext hdl
    have e3 := denote_ext hdt hst4.ext
    simp [denoteEntry, CEntryF.mapM, e1, e2, e3, hdk, bind, Option.bind, pure]

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:275-296 CKindF.mapM — a kind's names read
with effects, its expressions left out, upstream's. -/
theorem kindNamesT_run {pk : OleanPins} {s₀ : AState} {fn : UInt64 → AM (Option NIdx)}
    {gn : UInt64 → Option ConLeche.Name}
    (hn : ∀ a s s' y, Ctx pk s → Ext s₀.store s.store → fn a s = .ok (some y, s') →
      ParseStep s s' ∧ ∃ z, gn a = some z ∧ denoteN s'.store.ns y = some z)
    (kind : CKindF UInt64 UInt64) {k : CKindF NIdx Unit} {s s' : AState} (hctx : Ctx pk s)
    (hx0 : Ext s₀.store s.store)
    (h : (kind.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) (fun _ => pure ())) s
      = .ok (some k, s')) :
    ParseStep s s' ∧ ∃ kC, kind.mapM gn (fun _ => some ()) = some kC ∧
      denoteKindN s'.store k = some kC := by
  have hdN : ∀ {st st' : EStore} {y : NIdx} {z : ConLeche.Name}, Ext st st' →
      denoteN st.ns y = some z → denoteN st'.ns y = some z := fun hx hy => denoteN_ext hy hx
  have hlist := fun (l : List UInt64) {ys : List NIdx} {s s' : AState} (hc : Ctx pk s)
      (hx : Ext s₀.store s.store)
      (h : l.mapM (m := OptionT AM) (fun v => OptionT.mk (fn v)) s = .ok (some ys, s')) =>
    optT_list_runX (den := fun st => denoteN st.ns) (g := gn) hdN
      (fun a s s' y hc hx h => hn a s s' y hc hx h) l hc hx h
  cases kind with
  | ax u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | quot u =>
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | defn v hh sf =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h1
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | opaq v u =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h1
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    exact ⟨ParseStep.refl hctx.ok, _, rfl, rfl⟩
  | thm v all =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h1
    obtain ⟨ns, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst, zs, hz, hd⟩ := hlist all hctx hx0 h3
    refine ⟨hst, .thm () zs, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [denoteKindN, CKindF.mapM, hd, bind, Option.bind, pure]
  | induct np ni all cs nn ir iu irf =>
    simp only [CKindF.mapM] at h
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨bs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := hlist all hctx hx0 h1
    obtain ⟨hst2, ws, hw, hdw⟩ := hlist cs (hctx.step hst1) (hx0.trans hst1.ext) h3
    refine ⟨hst1.trans hst2, .induct np ni zs ws nn ir iu irf, ?_, ?_⟩
    · simp [CKindF.mapM, hz, hw, bind, Option.bind, pure]
    · have hd' := mapM_denoteN_ext hst2.ext hd
      simp [denoteKindN, CKindF.mapM, hd', hdw, bind, Option.bind, pure]
  | ctor ind ci np nf iu =>
    simp only [CKindF.mapM] at h
    obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h2
    obtain ⟨hst, z, hz, hd⟩ := hn ind s _ a hctx hx0 h1
    refine ⟨hst, .ctor z ci np nf iu, ?_, ?_⟩
    · simp [CKindF.mapM, hz, bind, Option.bind, pure]
    · simp [denoteKindN, CKindF.mapM, hd, bind, Option.bind, pure]
  | recur all np ni nmo nmi rules kk iu =>
    rw [recur_mapM] at h ⊢
    obtain ⟨as, s₁, h1, h2⟩ := OT.bind_ok h
    obtain ⟨rs, s₂, h3, h4⟩ := OT.bind_ok h2
    obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
    obtain ⟨hst1, zs, hz, hd⟩ := hlist all hctx hx0 h1
    obtain ⟨hst2, ws, hw, hdw⟩ := optT_list_runX (pk := pk) (s₀ := s₀)
      (den := fun st (x : NIdx × Nat × Unit) => do
        let c ← denoteN st.ns x.1
        let e ← (fun _ => some ()) x.2.2
        pure (c, x.2.1, e))
      (g := fun (x : UInt64 × Nat × UInt64) => do
        let c ← gn x.1
        let e ← (fun _ => some ()) x.2.2
        pure (c, x.2.1, e))
      (fun {st st' y z} hx hy => by
        cases hn' : denoteN st.ns y.1 with
        | none => simp [hn'] at hy
        | some n => simp only [hn'] at hy; simp only [denoteN_ext hn' hx]; exact hy)
      (fun x s s' y hc hx hrun => by
        obtain ⟨a, s₁, h1, h2⟩ := OT.bind_ok hrun
        obtain ⟨b, s₂, h3, h4⟩ := OT.bind_ok h2
        obtain ⟨rfl, rfl⟩ := OT.pure_ok h3
        obtain ⟨rfl, rfl⟩ := OT.pure_ok h4
        obtain ⟨hst, z, hz, hd⟩ := hn x.1 s _ a hc hx h1
        exact ⟨hst, (z, x.2.1, ()), by simp [hz], by simp [hd]⟩) rules (hctx.step hst1)
        (hx0.trans hst1.ext) h3
    refine ⟨hst1.trans hst2, .recur zs np ni nmo nmi ws kk iu, ?_, ?_⟩
    · rw [hz, hw]; rfl
    · have hd' := mapM_denoteN_ext hst2.ext hd
      rw [denoteKindN, recur_mapM, hd', hdw]; rfl

/-! ## A constant, a statement, several constants, read with a part's memo -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Present.lean:28 entryWith_spec — **a constant
read with a good memo is the specification's** (`entryAt`), and the memo stays good. -/
theorem entryWith_runR {pk : OleanPins} {r : Region} {m m' : SM} {c : Nat}
    {e : CEntryF NIdx EIdx} {s s' : AState} (hctx : Ctx pk s) (hm : SparseGood s.store r m)
    (h : ConRon.Arena.Frontend.Olean.entryWith pk r m c s = .ok ((m', some e), s')) :
    ParseStep s s' ∧ SparseGood s'.store r m' ∧ ∃ eC, entryAt r c = some eC ∧
      denoteEntry s'.store e = some eC := by
  generalize hF : ConRon.Arena.Frontend.Olean.entryWith pk r m c = f at h
  unfold ConRon.Arena.Frontend.Olean.entryWith at hF
  split at hF
  · subst hF; cases (AM.pure_ok h).1
  · rename_i sk hsk
    subst hF
    obtain ⟨u, s₁, h1, h⟩ := AM.bind_ok h
    rw [skelFits_run h1] at h
    obtain ⟨m₁, s₂, h2, h⟩ := AM.bind_ok h
    obtain ⟨hst2, hg2⟩ := memoRoots_runR hctx hm h2
    obtain ⟨o, s₃, h3, h⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    have hc2 := hctx.step hst2
    obtain ⟨hst3, eC, heC, hde⟩ := entryMapT_run (s₀ := s₂) (gn := nameP r) (ge := exprP r)
      (fun a s s' y hc hx h => memoName_runR hc (hg2.ext hx) h)
      (fun a s s' y hc hx h => memoExpr_runR hc (hg2.ext hx) h) sk hc2 (Ext.refl _) h3
    refine ⟨hst2.trans hst3, hg2.ext hst3.ext, eC, ?_, hde⟩
    simp only [entryAt, hsk, Option.bind_eq_bind, Option.bind_some,
      ConLeche.Frontend.Olean.sparseEntry_eq]
    exact heC

/-- con-leche: ConLeche/Verify/Frontend/Olean/Present.lean:43 stmtWith_spec — **a statement
and kind read with a good memo are the skeleton's** (`StmtSkel`), and the memo stays good. -/
theorem stmtWith_runR {pk : OleanPins} {r : Region} {m m' : SM} {c : Nat}
    {cv : ConRon.Arena.Frontend.Olean.StmtRec} {k : CKindF NIdx Unit} {s s' : AState}
    (hctx : Ctx pk s) (hm : SparseGood s.store r m)
    (h : ConRon.Arena.Frontend.Olean.stmtWith pk r m c s = .ok ((m', some (cv, k)), s')) :
    ParseStep s s' ∧ SparseGood s'.store r m' ∧ ∃ cvC kC, ConLeche.Driver.StmtSkel r c cvC kC ∧
      denoteStmt s'.store cv = some cvC ∧ denoteKindN s'.store k = some kC := by
  generalize hF : ConRon.Arena.Frontend.Olean.stmtWith pk r m c = f at h
  unfold ConRon.Arena.Frontend.Olean.stmtWith at hF
  split at hF
  · subst hF; cases (AM.pure_ok h).1
  · rename_i sk hsk
    subst hF
    obtain ⟨u, s₁, h1, h⟩ := AM.bind_ok h
    rw [skelFits_run h1] at h
    obtain ⟨m₁, s₂, h2, h⟩ := AM.bind_ok h
    obtain ⟨hst2, hg2⟩ := memoAddAll_runR (Or.inl rfl) _ hctx hm h2
    obtain ⟨m₂, s₃, h3, h⟩ := AM.bind_ok h
    obtain ⟨hst3, hg3⟩ := memoAdd_runR (Or.inr (Or.inr (Or.inl rfl))) (hctx.step hst2) hg2 h3
    obtain ⟨o, s₄, h4, h⟩ := AM.bind_ok h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    cases hv
    have hc3 := (hctx.step hst2).step hst3
    have hN := fun a s s' y hc (hx : Ext s₃.store (AState.store s)) h =>
      memoName_runR (pk := pk) (r := r) (m := m') (v := a) (x := y) (s := s) (s' := s') hc (hg3.ext hx) h
    have hE := fun a s s' y hc (hx : Ext s₃.store (AState.store s)) h =>
      memoExpr_runR (pk := pk) (r := r) (m := m') (v := a) (x := y) (s := s) (s' := s') hc (hg3.ext hx) h
    obtain ⟨n, t₁, g1, g⟩ := OT.bind_ok h4
    obtain ⟨hst4, zn, hzn, hdn⟩ := hN _ _ _ _ hc3 (Ext.refl _) g1
    obtain ⟨lps, t₂, g2, g⟩ := OT.bind_ok g
    obtain ⟨hst5, zl, hzl, hdl⟩ := optT_list_runX (s₀ := s₃) (den := fun st => denoteN st.ns)
      (g := nameP r) (fun hx hy => denoteN_ext hy hx) (fun a s s' y hc hx h => hN a s s' y hc hx h)
      sk.levelParams (hc3.step hst4) hst4.ext g2
    obtain ⟨ty, t₃, g3, g⟩ := OT.bind_ok g
    obtain ⟨hst6, zt, hzt, hdt⟩ := hE _ _ _ _ ((hc3.step hst4).step hst5) (hst4.ext.trans hst5.ext) g3
    obtain ⟨kk, t₄, g4, g⟩ := OT.bind_ok g
    obtain ⟨hst7, zk, hzk, hdk⟩ := kindNamesT_run (s₀ := s₃)
      (fun a s s' y hc hx h => hN a s s' y hc hx h) sk.kind
      (((hc3.step hst4).step hst5).step hst6) ((hst4.ext.trans hst5.ext).trans hst6.ext) g4
    obtain ⟨hv, rfl⟩ := OT.pure_ok g
    cases hv
    have hall := (((hst2.trans hst3).trans hst4).trans hst5).trans hst6 |>.trans hst7
    refine ⟨hall, hg3.ext (((hst4.trans hst5).trans hst6).trans hst7).ext, ⟨zn, zl, zt⟩, zk,
      ⟨sk, hsk, hzn, hzl, hzt, hzk⟩, ?_, hdk⟩
    have e1 := denoteN_ext hdn ((hst5.trans hst6).trans hst7).ext
    have e2 := mapM_denoteN_ext (hst6.trans hst7).ext hdl
    have e3 := denote_ext hdt hst7.ext
    simp [denoteStmt, e1, e2, e3, bind, Option.bind, pure]

/-- con-leche: ConLeche/Verify/Driver/ReachFrom.lean:887 entriesWith_spec — several constants
read with one good memo, each the specification's. -/
theorem entriesWith_runR {pk : OleanPins} {r : Region} :
    ∀ (ls : List Nat) {m m' : SM} {es : List (CEntryF NIdx EIdx)} {s s' : AState}, Ctx pk s →
      SparseGood s.store r m →
      ConRon.Arena.Modular.entriesWith pk r m ls s = .ok ((m', some es), s') →
      ParseStep s s' ∧ SparseGood s'.store r m' ∧ ∃ esC, ls.mapM (entryAt r) = some esC ∧
        es.mapM (denoteEntry s'.store) = some esC
  | [], m, m', es, s, s', hctx, hm, h => by
    rw [ConRon.Arena.Modular.entriesWith] at h
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq, Option.some.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨ParseStep.refl hctx.ok, hm, [], rfl, rfl⟩
  | l :: ls, m, m', es, s, s', hctx, hm, h => by
    rw [ConRon.Arena.Modular.entriesWith] at h
    obtain ⟨⟨m₁, o⟩, s₁, h1, h⟩ := AM.bind_ok h
    cases o with
    | none => cases (AM.pure_ok h).1
    | some e =>
    obtain ⟨hst1, hg1, eC, heC, hde⟩ := entryWith_runR hctx hm h1
    obtain ⟨⟨m₂, o'⟩, s₂, h2, h⟩ := AM.bind_ok h
    cases o' with
    | none => cases (AM.pure_ok h).1
    | some es' =>
    obtain ⟨hv, rfl⟩ := AM.pure_ok h
    simp only [Prod.mk.injEq, Option.some.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    obtain ⟨hst2, hg2, esC, hes, hdes⟩ := entriesWith_runR ls (hctx.step hst1) hg1 h2
    refine ⟨hst1.trans hst2, hg2, eC :: esC, ?_, ?_⟩
    · simp only [List.mapM_cons, heC, hes]; rfl
    · simp only [List.mapM_cons, denoteEntry_ext hst2.ext hde, hdes]; rfl

/-! ## Upstream's reads with a good memo answer -/

/-- con-leche: ConLeche/Frontend/Olean/Present.lean:26-30 entryWith — **upstream's read with a
good memo gives the specification's constant**, the memo good after. -/
theorem entryWith_complete {r : Region} {st : ConLeche.Frontend.Olean.SM} (hG : st.Good r) {c : Nat}
    {e : CEntryF ConLeche.Name Expr} (he : entryAt r c = some e) :
    ∃ st', ConLeche.Frontend.Olean.entryWith r st c = some (st', e) ∧ st'.Good r := by
  simp only [entryAt] at he
  obtain ⟨sk, hsk, he⟩ := bind_some_left he
  rw [ConLeche.Frontend.Olean.sparseEntry_eq] at he
  have hG' := ConLeche.Frontend.Olean.memoRoots_good hG sk
  refine ⟨_, ?_, hG'⟩
  simp only [ConLeche.Frontend.Olean.entryWith, hsk, Option.bind_eq_bind, Option.bind_some,
    ConLeche.Frontend.Olean.memoName_eq hG', ConLeche.Frontend.Olean.memoExpr_eq hG', he]
  rfl

/-- con-leche: ConLeche/Frontend/Olean/Present.lean:32-42 stmtWith — **upstream's read with a
good memo gives the skeleton's statement and kind**, the memo good after. -/
theorem stmtWith_complete {r : Region} {st : ConLeche.Frontend.Olean.SM} (hG : st.Good r) {c : Nat}
    {cv : ConstantVal} {k : CKindF ConLeche.Name Unit} (h : ConLeche.Driver.StmtSkel r c cv k) :
    ∃ st', ConLeche.Frontend.Olean.stmtWith r st c = some (st', cv, k) ∧ st'.Good r := by
  obtain ⟨sk, hsk, hn, hl, ht, hk⟩ := h
  have hG' : (ConLeche.Frontend.Olean.memoAdd r kExpr
      ((sk.name :: sk.levelParams).foldl (ConLeche.Frontend.Olean.memoAdd r kName) st)
      sk.type).Good r :=
    ConLeche.Frontend.Olean.memoAdd_good ConLeche.Frontend.Olean.isKind_expr
      (ConLeche.Frontend.Olean.foldl_memoAdd_good ConLeche.Frontend.Olean.isKind_name _ _ hG) _
  refine ⟨_, ?_, hG'⟩
  simp only [ConLeche.Frontend.Olean.stmtWith, hsk, Option.bind_eq_bind, Option.bind_some,
    ConLeche.Frontend.Olean.memoName_eq hG', ConLeche.Frontend.Olean.memoExpr_eq hG', hn, hl, ht, hk]
  rfl

theorem entriesWith_complete {r : Region} :
    ∀ (ls : List Nat) {st : ConLeche.Frontend.Olean.SM} {es : List (CEntryF ConLeche.Name Expr)},
      st.Good r → ls.mapM (entryAt r) = some es →
      ∃ st', ConLeche.Driver.entriesWith r st ls = some (st', es) ∧ st'.Good r
  | [], st, es, hG, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact ⟨st, rfl, hG⟩
  | l :: ls, st, es, hG, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨e, he, h⟩ := bind_some_left h
    obtain ⟨es', hes, h⟩ := bind_some_left h
    simp only [pure, Option.some.injEq] at h
    subst h
    obtain ⟨st₁, h1, hG1⟩ := entryWith_complete hG he
    obtain ⟨st₂, h2, hG2⟩ := entriesWith_complete ls hG1 hes
    refine ⟨st₂, ?_, hG2⟩
    simp only [ConLeche.Driver.entriesWith, h1, h2, bind, Option.bind, pure]

end ConRon.Bridge.Modular
