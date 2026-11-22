/-
# `ConRon.Refine2.Modular.ReachFuel` — the twin's worklist is monotone in its fuel

**Task #166, Theorem 2.**  A run of the twin's `reachGo` that succeeds with some fuel succeeds,
with the same answer, with more: so the Rust's accept at its own fuel (`u64` lengths plus
`1 <<< 24`) is the twin's at any fuel at least as large.
-/
import ConRon.Arena.Modular.Reach

namespace ConRon.Refine2.Modular

open ConRon.Arena

theorem reachGo_mono (fs : Arena.Frontend.Olean.OleanFs) (pk : Arena.Frontend.Olean.OleanPins)
    (sp : ConLeche.Frontend.Olean.Roots) (env : Modular.ReachEnv) :
    ∀ (n k : Nat) (L : Modular.ReachLog) (c : Modular.ReachCache) (s : AState) r,
      (Modular.reachGo fs pk sp env n L c).run s = .ok r →
      (Modular.reachGo fs pk sp env (n + k) L c).run s = .ok r := by
  intro n
  induction n with
  | zero =>
    intro k L c s r h
    rw [Modular.reachGo.eq_def] at h ⊢
    dsimp only at h ⊢
    cases hs : L.stack with
    | nil =>
      simp only [hs] at h ⊢
      by_cases hp : c.partners.isEmpty = true
      · simp only [hp, ↓reduceIte] at h ⊢; exact h
      · simp only [hp] at h; cases h
    | cons x rest => simp only [hs] at h; cases h
  | succ n ih =>
    intro k L c s r h
    rw [show n + 1 + k = (n + k) + 1 by omega]
    rw [Modular.reachGo.eq_def] at h ⊢
    dsimp only at h ⊢
    cases hs : L.stack with
    | nil =>
      simp only [hs] at h ⊢
      by_cases hp : c.partners.isEmpty = true
      · simp only [hp, ↓reduceIte] at h ⊢; exact h
      · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [StateT.run_bind] at h ⊢
        cases h1 : (Modular.reachPartners fs pk sp env L c).run s with
        | error e => rw [h1] at h; cases h
        | ok p =>
          rw [h1] at h
          exact ih k _ _ _ r h
    | cons x rest =>
      simp only [hs] at h ⊢
      rw [StateT.run_bind] at h ⊢
      cases h1 : (Modular.reachRead fs pk sp env { L with stack := rest } c x).run s with
      | error e => rw [h1] at h; cases h
      | ok p =>
        rw [h1] at h
        exact ih k _ _ _ r h

/-! ## The read order's positions are positions of the records -/

/-- The owner map's fold: every position it stores is below its counter. -/
theorem ownerMap_fold_lt :
    ∀ (ds : List IDeclaration) (acc : Std.HashMap NIdx Nat × Nat) (s : AState) r,
      (∀ (n : NIdx) (j : Nat), acc.1[n]? = some j → j < acc.2) →
      (ds.foldlM (fun (acc : Std.HashMap NIdx Nat × Nat) d => do
        let ns ← Modular.declNames d
        pure (ns.foldl (fun (m : Std.HashMap NIdx Nat) n => m.insert n acc.2) acc.1, acc.2 + 1)) acc).run s = .ok r →
      r.1.2 = acc.2 + ds.length ∧ ∀ (n : NIdx) (j : Nat), r.1.1[n]? = some j → j < r.1.2
  | [], acc, s, r, hacc, h => by
    simp only [List.foldlM_nil] at h
    cases h; exact ⟨by simp, hacc⟩
  | d :: ds, acc, s, r, hacc, h => by
    rw [List.foldlM_cons, StateT.run_bind] at h
    cases h1 : (do
        let ns ← Modular.declNames d
        pure (ns.foldl (fun (m : Std.HashMap NIdx Nat) n => m.insert n acc.2) acc.1, acc.2 + 1) : AM _).run s with
    | error e => rw [h1] at h; cases h
    | ok p =>
      rw [h1] at h
      obtain ⟨acc', s'⟩ := p
      have hstep : acc'.2 = acc.2 + 1 ∧ ∀ (n : NIdx) (j : Nat), acc'.1[n]? = some j → j < acc'.2 := by
        rw [StateT.run_bind] at h1
        cases h2 : (Modular.declNames d).run s with
        | error e => rw [h2] at h1; cases h1
        | ok q =>
          rw [h2] at h1
          obtain ⟨ns, s2⟩ := q
          cases h1
          refine ⟨rfl, ?_⟩
          have key : ∀ (l : List NIdx) (m : Std.HashMap NIdx Nat), (∀ (n : NIdx) (j : Nat), m[n]? = some j → j < acc.2 + 1) →
              ∀ (n : NIdx) (j : Nat), (l.foldl (fun (m : Std.HashMap NIdx Nat) n => m.insert n acc.2) m)[n]? = some j → j < acc.2 + 1 := by
            intro l
            induction l with
            | nil => intro m hm; simpa using hm
            | cons x xs ih =>
              intro m hm
              apply ih
              intro n j hj
              rw [Std.HashMap.getElem?_insert] at hj
              split at hj
              · cases hj; omega
              · exact hm n j hj
          exact key ns acc.1 (fun n j hj => by have := hacc n j hj; omega)
      obtain ⟨e1, e2⟩ := ownerMap_fold_lt ds acc' s' r hstep.2 h
      refine ⟨by rw [e1, hstep.1]; simp; omega, e2⟩

theorem ownerMap_lt (ds : List IDeclaration) (s : AState) r
    (h : (Modular.ownerMap ds).run s = .ok r) : ∀ (n : NIdx) (j : Nat), r.1[n]? = some j → j < ds.length := by
  unfold Modular.ownerMap at h
  rw [StateT.run_bind] at h
  cases h1 : (ds.foldlM (fun (acc : Std.HashMap NIdx Nat × Nat) d => do
        let ns ← Modular.declNames d
        pure (ns.foldl (fun (m : Std.HashMap NIdx Nat) n => m.insert n acc.2) acc.1, acc.2 + 1)) ({}, 0)).run s with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rw [h1] at h
    cases h
    obtain ⟨e1, e2⟩ := ownerMap_fold_lt ds ({}, 0) s p (by simp) h1
    intro n j hj
    have := e2 n j hj
    omega

/-- A read-order state whose positions are below `n`. -/
def OrderLt (n : Nat) (st : Modular.SortSt) : Prop := ∀ j ∈ st.order.toList, j < n

section sort
variable (ds : Array IDeclaration) (rds : Array (List NIdx)) (owner : Std.HashMap NIdx Nat) (n : Nat)
  (hown : ∀ (y : NIdx) (j : Nat), owner[y]? = some j → j < n)
include hown

theorem sortVisitList_lt (fuel : Nat)
    (hv : ∀ i path ys st s r, i < n → OrderLt n st →
      (Modular.sortVisit ds rds owner fuel i path ys st).run s = .ok r → OrderLt n r.1) :
    ∀ (ys : List NIdx) i path st s r, OrderLt n st →
      (Modular.sortVisitList ds rds owner fuel i path ys st).run s = .ok r → OrderLt n r.1
  | [], i, path, st, s, r, hst, h => by
    rw [Modular.sortVisitList] at h
    cases h; exact hst
  | y :: ys, i, path, st, s, r, hst, h => by
    rw [Modular.sortVisitList] at h
    cases hy : owner[y]? with
    | none =>
      rw [hy] at h
      simp only at h
      rw [StateT.run_bind] at h
      cases h2 : (readName y).run s with
      | error e => rw [h2] at h; cases h
      | ok q => rw [h2] at h; cases h
    | some j =>
      rw [hy] at h
      simp only at h
      split at h
      · exact sortVisitList_lt fuel hv ys i path st s r hst h
      · split at h
        · rw [StateT.run_bind] at h
          cases h2 : (Modular.sortCycle ds i j y).run s with
          | error e => rw [h2] at h; cases h
          | ok q => rw [h2] at h; cases h
        · rw [StateT.run_bind] at h
          cases h2 : (Modular.sortVisit ds rds owner fuel j (path.insert j) (rds.getD j []) st).run s with
          | error e => rw [h2] at h; cases h
          | ok q =>
            rw [h2] at h
            have := hv j (path.insert j) (rds.getD j []) st s q (hown y j hy) hst h2
            exact sortVisitList_lt fuel hv ys i path q.1 q.2 r this h

theorem sortVisit_lt : ∀ (fuel : Nat) i path ys st s r, i < n → OrderLt n st →
    (Modular.sortVisit ds rds owner fuel i path ys st).run s = .ok r → OrderLt n r.1
  | 0, i, path, ys, st, s, r, _, _, h => by
    rw [Modular.sortVisit] at h; cases h
  | fuel + 1, i, path, ys, st, s, r, hi, hst, h => by
    rw [Modular.sortVisit, StateT.run_bind] at h
    cases h2 : (Modular.sortVisitList ds rds owner fuel i path ys st).run s with
    | error e => rw [h2] at h; cases h
    | ok q =>
      rw [h2] at h
      cases h
      have hq := sortVisitList_lt ds rds owner n hown fuel (sortVisit_lt fuel) ys i path st s q hst h2
      intro j hj
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact hq j hj
      · exact hi

theorem sortFrom_lt (fuel : Nat) : ∀ (is : List Nat) st s r, (∀ i ∈ is, i < n) → OrderLt n st →
    (Modular.sortFrom ds rds owner fuel is st).run s = .ok r → OrderLt n r.1
  | [], st, s, r, _, hst, h => by
    rw [Modular.sortFrom] at h; cases h; exact hst
  | i :: is, st, s, r, his, hst, h => by
    rw [Modular.sortFrom] at h
    split at h
    · exact sortFrom_lt fuel is st s r (fun k hk => his k (List.mem_cons_of_mem _ hk)) hst h
    · rw [StateT.run_bind] at h
      cases h2 : (Modular.sortVisit ds rds owner fuel i (({} : Std.HashSet Nat).insert i) (rds.getD i []) st).run s with
      | error e => rw [h2] at h; cases h
      | ok q =>
        rw [h2] at h
        have := sortVisit_lt ds rds owner n hown fuel i _ _ st s q (his i (List.mem_cons_self ..)) hst h2
        exact sortFrom_lt fuel is q.1 q.2 r (fun k hk => his k (List.mem_cons_of_mem _ hk)) this h

end sort

/-- **The read order's positions are positions of the records.** -/
theorem readOrder_lt (ds : Array IDeclaration) (rds : Array (List NIdx)) (s : AState) r
    (h : (Modular.readOrder ds rds).run s = .ok r) : ∀ j ∈ r.1.toList, j < ds.size := by
  unfold Modular.readOrder at h
  rw [StateT.run_bind] at h
  cases h1 : (Modular.ownerMap ds.toList).run s with
  | error e => rw [h1] at h; cases h
  | ok p =>
    rw [h1] at h
    have hown := ownerMap_lt ds.toList s p h1
    rw [show (Except.ok p : Except CheckError _) = pure p from rfl, pure_bind, StateT.run_bind] at h
    cases h2 : (Modular.sortFrom ds rds p.1 (ds.size + 1) (List.range ds.size) {}).run p.2 with
    | error e => rw [h2] at h; cases h
    | ok q =>
      rw [h2] at h
      cases h
      exact sortFrom_lt ds rds p.1 ds.size (by simpa using hown) (ds.size + 1) _ {} p.2 q
        (fun i hi => List.mem_range.mp hi) (fun j hj => by simp at hj) h2

end ConRon.Refine2.Modular
