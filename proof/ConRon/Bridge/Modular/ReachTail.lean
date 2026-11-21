/-
# `ConRon.Bridge.Modular.ReachTail` — the reach's tail, Theorem 1 (task #166)

The pure end of the twin's `reach` (`Arena/Modular/Reach.lean`) against upstream's
(`ConLeche/Driver/Reach.lean`): the read order (`readOrder_run`: the same positions, over the
denoted records and reads; `readOrder_lt`: every position a record's), the records at those
positions (`inReadOrder_rel`), the validation (`validateCtx_run`).  Simulations in the Closure
run style (`AM.bind_ok`), no `sym`/`vcgen`: the walks are over handle-keyed maps.
-/
module

public import ConRon.Bridge.Modular.Copies
public import ConRon.Bridge.Modular.Graph

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean

/-! ## The read order -/

/-- A twin sort state as upstream's (the same fields). -/
@[expose] def sortC (r : ConRon.Arena.Modular.SortSt) : ConLeche.Driver.SortSt :=
  ⟨r.order, r.placed⟩

theorem getD_listRel {st : EStore} {rds : Array (List NIdx)} {rdsC : Array (List ConLeche.Name)}
    (h : ListRel (fun (a : List NIdx) (b : List ConLeche.Name) => ListRel (NR st) a b)
      rds.toList rdsC.toList) (j : Nat) :
    ListRel (NR st) (rds.getD j []) (rdsC.getD j []) := by
  have := listRel_getElem? h j
  simp only [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]
  revert this
  generalize rds.toList[j]? = a
  generalize rdsC.toList[j]? = b
  intro this
  cases this with
  | none => exact .nil
  | some h => exact h

section SortWalk

variable {st : EStore} (hw : NStoreWF st.ns)
  {ds : Array IDeclaration} {dsC : Array Declaration}
  {rds : Array (List NIdx)} {rdsC : Array (List ConLeche.Name)}
  {owner : Std.HashMap NIdx Nat} {ownerC : Std.HashMap ConLeche.Name Nat}
  (hown : HMRel (· = ·) st owner ownerC)
  (hrds : ListRel (fun (a : List NIdx) (b : List ConLeche.Name) => ListRel (NR st) a b)
    rds.toList rdsC.toList)
include hw hown hrds

/-- con-leche: ConLeche/Driver/Reach.lean:879-901 sortVisit — **the twin's post-order walk is
upstream's**: a twin `sortVisit` at fuel `f` accepting leaves the state alone and is upstream's
at fuel `f`; its list part at `f` is upstream's walk at `f + 1` before the push of `i`. -/
theorem sortVisit_run : ∀ (f : Nat),
    (∀ (i : Nat) (path : Std.HashSet Nat) (ys : List NIdx) (ysC : List ConLeche.Name)
      (s0 : ConRon.Arena.Modular.SortSt) {s s' : AState} {r : ConRon.Arena.Modular.SortSt},
      s.store = st → ListRel (NR st) ys ysC →
      ConRon.Arena.Modular.sortVisit ds rds owner f i path ys s0 s = .ok (r, s') →
      s' = s ∧ ConLeche.Driver.sortVisit dsC rdsC ownerC f i path ysC (sortC s0) = .ok (sortC r)) ∧
    (∀ (i : Nat) (path : Std.HashSet Nat) (ys : List NIdx) (ysC : List ConLeche.Name)
      (s0 : ConRon.Arena.Modular.SortSt) {s s' : AState} {r : ConRon.Arena.Modular.SortSt},
      s.store = st → ListRel (NR st) ys ysC →
      ConRon.Arena.Modular.sortVisitList ds rds owner f i path ys s0 s = .ok (r, s') →
      s' = s ∧ ConLeche.Driver.sortVisit dsC rdsC ownerC (f + 1) i path ysC (sortC s0) =
        .ok ⟨r.order.push i, r.placed.insert i⟩)
  | 0 => by
    refine ⟨fun i path ys ysC s0 s s' r _ _ h => ?_, ?_⟩
    · simp only [ConRon.Arena.Modular.sortVisit] at h
      exact absurd h fail_not_ok
    · intro i path ys ysC s0 s s' r hs hys h
      induction hys generalizing s0 s s' r with
      | nil =>
        simp only [ConRon.Arena.Modular.sortVisitList] at h
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h
        simp [ConLeche.Driver.sortVisit, sortC]
      | @cons y yC ys ysC hy hys ih =>
        simp only [ConRon.Arena.Modular.sortVisitList] at h
        rw [ConLeche.Driver.sortVisit]
        have hg := hown.get_eq hw hy
        cases ho : owner[y]? with
        | none =>
          rw [ho] at h
          obtain ⟨_, _, _, h'⟩ := AM.bind_ok h
          exact absurd h' fail_not_ok
        | some j =>
          rw [ho] at hg
          rw [← hg]
          simp only [ho] at h
          dsimp only
          have hsc : (sortC s0).placed = s0.placed := rfl
          rw [hsc]
          cases hj : (j == i || s0.placed.contains j) with
          | true =>
            simp only [hj, ↓reduceIte] at h ⊢
            exact ih s0 hs h
          | false =>
            simp only [hj, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases hp : path.contains j with
            | true =>
              simp only [hp, ↓reduceIte] at h
              obtain ⟨_, _, _, h'⟩ := AM.bind_ok h
              exact absurd h' fail_not_ok
            | false =>
              simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨_, _, h1, _⟩ := AM.bind_ok h
              simp only [ConRon.Arena.Modular.sortVisit] at h1
              exact absurd h1 fail_not_ok
  | f + 1 => by
    obtain ⟨-, ihL⟩ := sortVisit_run f
    have ihV : ∀ (i : Nat) (path : Std.HashSet Nat) (ys : List NIdx) (ysC : List ConLeche.Name)
        (s0 : ConRon.Arena.Modular.SortSt) {s s' : AState} {r : ConRon.Arena.Modular.SortSt},
        s.store = st → ListRel (NR st) ys ysC →
        ConRon.Arena.Modular.sortVisit ds rds owner (f + 1) i path ys s0 s = .ok (r, s') →
        s' = s ∧ ConLeche.Driver.sortVisit dsC rdsC ownerC (f + 1) i path ysC (sortC s0) =
          .ok (sortC r) := by
      intro i path ys ysC s0 s s' r hs hys h
      simp only [ConRon.Arena.Modular.sortVisit] at h
      obtain ⟨r1, s1, h1, h2⟩ := AM.bind_ok h
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨rfl, e⟩ := ihL i path ys ysC s0 hs hys h1
      exact ⟨rfl, by rw [e]; rfl⟩
    have hL : ∀ (i : Nat) (path : Std.HashSet Nat) (ys : List NIdx) (ysC : List ConLeche.Name)
        (s0 : ConRon.Arena.Modular.SortSt) {s s' : AState} {r : ConRon.Arena.Modular.SortSt},
        s.store = st → ListRel (NR st) ys ysC →
        ConRon.Arena.Modular.sortVisitList ds rds owner (f + 1) i path ys s0 s = .ok (r, s') →
        s' = s ∧ ConLeche.Driver.sortVisit dsC rdsC ownerC (f + 1 + 1) i path ysC (sortC s0) =
          .ok ⟨r.order.push i, r.placed.insert i⟩ := by
      intro i path ys ysC s0 s s' r hs hys h
      induction hys generalizing s0 s s' r with
      | nil =>
        simp only [ConRon.Arena.Modular.sortVisitList] at h
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h
        simp [ConLeche.Driver.sortVisit, sortC]
      | @cons y yC ys ysC hy hys ih =>
        simp only [ConRon.Arena.Modular.sortVisitList] at h
        rw [ConLeche.Driver.sortVisit]
        have hg := hown.get_eq hw hy
        cases ho : owner[y]? with
        | none =>
          rw [ho] at h
          obtain ⟨_, _, _, h'⟩ := AM.bind_ok h
          exact absurd h' fail_not_ok
        | some j =>
          rw [ho] at hg
          rw [← hg]
          simp only [ho] at h
          dsimp only
          have hsc : (sortC s0).placed = s0.placed := rfl
          rw [hsc]
          cases hj : (j == i || s0.placed.contains j) with
          | true =>
            simp only [hj, ↓reduceIte] at h ⊢
            exact ih s0 hs h
          | false =>
            simp only [hj, Bool.false_eq_true, ↓reduceIte] at h ⊢
            cases hp : path.contains j with
            | true =>
              simp only [hp, ↓reduceIte] at h
              obtain ⟨_, _, _, h'⟩ := AM.bind_ok h
              exact absurd h' fail_not_ok
            | false =>
              simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
              obtain ⟨r1, s1, h1, h2⟩ := AM.bind_ok h
              obtain ⟨rfl, e1⟩ := ihV j (path.insert j) (rds.getD j []) (rdsC.getD j []) s0 hs
                (getD_listRel hrds j) h1
              rw [e1]
              exact ih r1 hs h2
    exact ⟨ihV, hL⟩

/-- con-leche: ConLeche/Driver/Reach.lean:903-912 sortFrom — the twin's `sortFrom` is upstream's. -/
theorem sortFrom_run (fuel : Nat) : ∀ (is : List Nat) (s0 : ConRon.Arena.Modular.SortSt)
    {s s' : AState} {r : ConRon.Arena.Modular.SortSt}, s.store = st →
    ConRon.Arena.Modular.sortFrom ds rds owner fuel is s0 s = .ok (r, s') →
    s' = s ∧ ConLeche.Driver.sortFrom dsC rdsC ownerC fuel is (sortC s0) = .ok (sortC r)
  | [], s0, s, s', r, _, h => by
    simp only [ConRon.Arena.Modular.sortFrom] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨rfl, rfl⟩
  | i :: is, s0, s, s', r, hs, h => by
    simp only [ConRon.Arena.Modular.sortFrom] at h
    rw [ConLeche.Driver.sortFrom]
    have hsc : (sortC s0).placed = s0.placed := rfl
    rw [hsc]
    cases hp : s0.placed.contains i with
    | true =>
      simp only [hp, ↓reduceIte] at h ⊢
      exact sortFrom_run fuel is s0 hs h
    | false =>
      simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨r1, s1, h1, h2⟩ := AM.bind_ok h
      obtain ⟨rfl, e1⟩ := (sortVisit_run hw hown hrds fuel).1 i _ _ _ s0 hs (getD_listRel hrds i) h1
      rw [e1]
      exact sortFrom_run fuel is r1 hs h2

end SortWalk

theorem denoteDecls_length {st : EStore} :
    ∀ {l : List IDeclaration} {l' : List Declaration}, denoteDecls st l = some l' →
      l.length = l'.length
  | [], l', h => by simp only [denoteDecls, Option.some.injEq] at h; subst h; rfl
  | d :: l, l', h => by
    simp only [denoteDecls] at h
    cases h1 : Frontend.denoteDecl st d with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : denoteDecls st l with
    | none => rw [h1, h2] at h; simp at h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    simp [denoteDecls_length h2]

/-- con-leche: ConLeche/Driver/Reach.lean:914-918 readOrder — **the twin's read order is
upstream's**, over the denoted records and reads: the same positions. -/
theorem readOrder_run {s s' : AState} {ds : Array IDeclaration} {dsC : Array Declaration}
    {rds : Array (List NIdx)} {rdsC : Array (List ConLeche.Name)} {o : Array Nat}
    (hok : DriverOK s) (hd : denoteDecls s.store ds.toList = some dsC.toList)
    (hrds : ListRel (fun (a : List NIdx) (b : List ConLeche.Name) => ListRel (NR s.store) a b)
      rds.toList rdsC.toList)
    (h : ConRon.Arena.Modular.readOrder ds rds s = .ok (o, s')) :
    CStep s s' ∧ ConLeche.Driver.readOrder dsC rdsC = .ok o := by
  simp only [ConRon.Arena.Modular.readOrder] at h
  obtain ⟨owner, s1, h1, h2⟩ := AM.bind_ok h
  obtain ⟨c1, hown⟩ := ownerMap_run hok hd h1
  obtain ⟨r, s2, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
  have hw := nsWF_of_StateOK c1.ok.state
  have hrds' := ListRel.mono' (fun a b (h : ListRel (NR s.store) a b) =>
    ListRel.mono' (fun x y (hx : NR s.store x y) => (denoteN_ext hx c1.ext : NR s1.store x y)) h) hrds
  have hsz : ds.size = dsC.size := by
    have := denoteDecls_length hd
    simpa using this
  obtain ⟨rfl, e⟩ := sortFrom_run hw hown hrds' (ds.size + 1) (List.range ds.size) {} rfl h3
  refine ⟨c1, ?_⟩
  simp only [ConLeche.Driver.readOrder, ← hsz]
  rw [show (({} : ConLeche.Driver.SortSt)) = sortC {} from rfl, e]
  rfl

end ConRon.Bridge.Modular
