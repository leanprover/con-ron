/-
# `ConRon.Bridge.Modular.ReachMemo` — reads with a part's memo, Theorem 1 (task #166)

The reach reads a part's constants with one memo per part (`entryWith`, `stmtWith`,
`entriesWith`, `Arena/Frontend/Olean/Present.lean`).  A memo whose every handle denotes the
specification's value at its location (`SMGood`) stays so under the twin's root reads
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
      IsKind k → SMGood s.store r m → FrontierGood s.store r b →
      ConRon.Arena.Frontend.Olean.sGo pk r b k g m s = .ok (none, s') → ParseStep s s' := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
  intro k m s s' hok hpk hk hm hb h
  have hkids : ∀ (fs : List (Nat × UInt8 × Bool)) {m : SM} {s s' : AState} {o : Option SM},
      StateOK s → NullsRel s.store pk → (∀ f ∈ fs, IsKind f.2.1) → SMGood s.store r m →
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
            obtain ⟨hst1, hg1, -, -⟩ := sGo_run c hok hpk hk' hm hb h1
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
    {v : UInt64} {s s' : AState} (hctx : Ctx pk s) (hm : SMGood s.store r m)
    (h : ConRon.Arena.Frontend.Olean.memoAdd pk r k m v s = .ok (m', s')) :
    ParseStep s s' ∧ SMGood s'.store r m' := by
  generalize hF : ConRon.Arena.Frontend.Olean.memoAdd pk r k m v = f at h
  unfold ConRon.Arena.Frontend.Olean.memoAdd at hF
  split at hF
  · rename_i c _
    subst hF
    obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok h
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨sGo_none c hctx.ok hctx.nulls hk hm (FrontierGood.empty _ _) h1, SMGood.empty _ _⟩
    | some m₁ =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨hst, hg, -, -⟩ := sGo_run c hctx.ok hctx.nulls hk hm (FrontierGood.empty _ _) h1
      exact ⟨hst, hg⟩
  · subst hF
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hctx.ok, hm⟩

end ConRon.Bridge.Modular
