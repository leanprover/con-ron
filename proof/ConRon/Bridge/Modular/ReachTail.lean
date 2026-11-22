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
public import ConRon.Bridge.Frontend.Olean.Records

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConLeche.Frontend.Olean (Copy CKindF)

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

/-! ## The read order's positions are records' -/

/-- Upstream's owner map along the records from position `j`: every value a position below
`j + l.length`, or the start map's. -/
theorem omGo_lt : ∀ (l : List Declaration) (j : Nat) (m : Std.HashMap ConLeche.Name Nat)
    (y : ConLeche.Name) (v : Nat), (omGo l j m)[y]? = some v → v < j + l.length ∨ m[y]? = some v
  | [], j, m, y, v, h => .inr h
  | d :: l, j, m, y, v, h => by
    rcases omGo_lt l (j + 1) _ y v h with h | h
    · exact .inl (by simp at h ⊢; omega)
    · have key : ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat),
          (ns.foldl (fun m y => m.insert y j) m)[y]? = some v → v = j ∨ m[y]? = some v := by
        intro ns
        induction ns with
        | nil => exact fun m h => .inr h
        | cons n ns ih =>
          intro m h
          rcases ih _ h with h | h
          · exact .inl h
          · rw [Std.HashMap.getElem?_insert] at h
            split at h
            · exact .inl (Option.some.inj h).symm
            · exact .inr h
      rcases key _ m h with h | h
      · exact .inl (by simp; omega)
      · exact .inr h

theorem ownerMap_lt {ds : Array Declaration} {y : ConLeche.Name} {v : Nat}
    (h : (ConLeche.Driver.ownerMap ds)[y]? = some v) : v < ds.size := by
  rw [ownerMap_eq] at h
  rcases omGo_lt ds.toList 0 {} y v h with h | h
  · simpa using h
  · simp at h

theorem sortVisit_lt {ds : Array Declaration} {rds : Array (List ConLeche.Name)}
    {owner : Std.HashMap ConLeche.Name Nat} {n : Nat}
    (hown : ∀ (y : ConLeche.Name) (v : Nat), owner[y]? = some v → v < n) :
    ∀ (fuel i : Nat) (path : Std.HashSet Nat) (ys : List ConLeche.Name)
      (st st' : ConLeche.Driver.SortSt), i < n → (∀ x ∈ st.order.toList, x < n) →
      ConLeche.Driver.sortVisit ds rds owner fuel i path ys st = .ok st' →
      ∀ x ∈ st'.order.toList, x < n
  | 0, _, _, _, _, _, _, _, h => by rw [ConLeche.Driver.sortVisit] at h; cases h
  | fuel + 1, i, path, [], st, st', hi, hst, h => by
    rw [ConLeche.Driver.sortVisit] at h
    cases h
    intro x hx
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hst x hx
    · exact hi
  | fuel + 1, i, path, y :: ys, st, st', hi, hst, h => by
    rw [ConLeche.Driver.sortVisit] at h
    split at h
    · cases h
    · next j hj =>
      split at h
      · exact sortVisit_lt hown (fuel + 1) i path ys st st' hi hst h
      · split at h
        · cases h
        · split at h
          · cases h
          · next st₁ h₁ =>
            exact sortVisit_lt hown (fuel + 1) i path ys st₁ st' hi
              (sortVisit_lt hown fuel j _ _ st st₁ (hown y j hj) hst h₁) h
termination_by fuel _ _ ys => (fuel, ys.length)

theorem sortFrom_lt {ds : Array Declaration} {rds : Array (List ConLeche.Name)}
    {owner : Std.HashMap ConLeche.Name Nat} {n fuel : Nat}
    (hown : ∀ (y : ConLeche.Name) (v : Nat), owner[y]? = some v → v < n) :
    ∀ (is : List Nat) (st st' : ConLeche.Driver.SortSt), (∀ i ∈ is, i < n) →
      (∀ x ∈ st.order.toList, x < n) →
      ConLeche.Driver.sortFrom ds rds owner fuel is st = .ok st' → ∀ x ∈ st'.order.toList, x < n
  | [], st, st', _, hst, h => by rw [ConLeche.Driver.sortFrom] at h; cases h; exact hst
  | i :: is, st, st', his, hst, h => by
    rw [ConLeche.Driver.sortFrom] at h
    split at h
    · exact sortFrom_lt hown is st st' (fun i hi => his i (List.mem_cons_of_mem _ hi)) hst h
    · split at h
      · cases h
      · next st₁ h₁ =>
        exact sortFrom_lt hown is st₁ st' (fun i hi => his i (List.mem_cons_of_mem _ hi))
          (sortVisit_lt hown fuel i _ _ st st₁ (his i (List.mem_cons_self ..)) hst h₁) h

/-- con-leche: ConLeche/Driver/Reach.lean:914-918 readOrder — **every position of the read
order is a record's.** -/
theorem readOrder_lt {ds : Array Declaration} {rds : Array (List ConLeche.Name)} {o : Array Nat}
    (h : ConLeche.Driver.readOrder ds rds = .ok o) : ∀ j ∈ o.toList, j < ds.size := by
  unfold ConLeche.Driver.readOrder at h
  cases hs : ConLeche.Driver.sortFrom ds rds (ConLeche.Driver.ownerMap ds) (ds.size + 1)
      (List.range ds.size) {} with
  | error e => rw [hs] at h; cases h
  | ok st =>
    rw [hs] at h
    cases h
    exact sortFrom_lt (fun y v hv => ownerMap_lt hv) _ {} st (fun i hi => List.mem_range.mp hi)
      (by simp) hs

/-! ## The records in read order -/

theorem listRel_append' {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β}, ListRel R a b → ListRel R c d →
      ListRel R (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons x h1, h2 => .cons x (listRel_append' h1 h2)

theorem inReadOrder_go {st : EStore} {ctx : Array IDeclaration} {ctxC : Array Declaration}
    {homes : Array NIdx} {homesC : Array ConLeche.Name}
    (f : Array IDeclaration × Array NIdx → Nat → Array IDeclaration × Array NIdx)
    (hf : ∀ acc j d h, ctx[j]? = some d → homes[j]? = some h → f acc j = (acc.1.push d, acc.2.push h))
    (hc : denoteDecls st ctx.toList = some ctxC.toList)
    (hh : ListRel (NR st) homes.toList homesC.toList) :
    ∀ (o : List Nat) (a : Array IDeclaration × Array NIdx) (aC : List Declaration)
      (bC : List ConLeche.Name),
      (∀ j ∈ o, j < ctx.size ∧ j < homes.size) →
      denoteDecls st a.1.toList = some aC → ListRel (NR st) a.2.toList bC →
      denoteDecls st (o.foldl f a).1.toList = some (aC ++ o.map (fun j => ctxC[j]?.getD default)) ∧
        ListRel (NR st) (o.foldl f a).2.toList (bC ++ o.map (fun j => homesC[j]?.getD default))
  | [], a, aC, bC, _, h1, h2 => by simpa using ⟨h1, h2⟩
  | j :: o, a, aC, bC, hj, h1, h2 => by
    obtain ⟨hj1, hj2⟩ := hj j (List.mem_cons_self ..)
    have hc' : ctx[j]? = some ctx[j] := Array.getElem?_eq_getElem hj1
    have hh' : homes[j]? = some homes[j] := Array.getElem?_eq_getElem hj2
    obtain ⟨dC, hdC, hd⟩ := denoteDecls_get hc (k := j) (e := ctx[j])
      (by rw [Array.getElem?_toList]; exact hc')
    have hgc : ctxC[j]?.getD default = dC := by
      rw [← Array.getElem?_toList, hdC]; rfl
    obtain ⟨hjC, hr⟩ := listRel_get hh (i := j) (by simpa using hj2)
    have hgh : homesC[j]?.getD default = homesC.toList[j] := by
      rw [← Array.getElem?_toList, List.getElem?_eq_getElem hjC]; rfl
    rw [List.foldl_cons, hf a j _ _ hc' hh']
    have := inReadOrder_go f hf hc hh o (a.1.push ctx[j], a.2.push homes[j]) (aC ++ [dC])
      (bC ++ [homesC.toList[j]]) (fun k hk => hj k (List.mem_cons_of_mem _ hk))
      (by simpa using denoteDecls_snoc hd h1)
      (by simpa using listRel_append' h2 (.cons (by simpa using hr) .nil))
    simpa [hgc, hgh] using this

/-- con-leche: ConLeche/Driver/Reach.lean:958-959 reachWith — **the records and homes in read
order**: at positions every one a record's, the twin's `inReadOrder` is upstream's maps. -/
theorem inReadOrder_rel {st : EStore} {L : ConRon.Arena.Modular.ReachLog}
    {ctxC : Array Declaration} {homesC : Array ConLeche.Name} {o : Array Nat}
    (hc : denoteDecls st L.ctx.toList = some ctxC.toList)
    (hh : ListRel (NR st) L.homes.toList homesC.toList)
    (hj : ∀ j ∈ o.toList, j < L.ctx.size ∧ j < L.homes.size) :
    denoteDecls st (ConRon.Arena.Modular.inReadOrder L o).1.toList =
        some (o.map (fun j => ctxC[j]?.getD default)).toList ∧
      ListRel (NR st) (ConRon.Arena.Modular.inReadOrder L o).2.toList
        (o.map (fun j => homesC[j]?.getD default)).toList := by
  unfold ConRon.Arena.Modular.inReadOrder
  rw [← Array.foldl_toList, Array.toList_map, Array.toList_map]
  refine inReadOrder_go _ ?_ hc hh o.toList (#[], #[]) [] [] hj rfl .nil
  intro acc j d h h1 h2
  simp only [h1, h2]

/-! ## The read order in the reach's shapes -/

/-! ## The clashes' copies by name -/

/-- A module's name for messages, read back (`HeaderLoads.nameAt`). -/
theorem nameAt_rel {st : EStore} {pk : ConRon.Arena.Frontend.Olean.OleanPins}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (hn : NullsRel st pk) (hl : LoadsRel st ld ldC) (i : Nat) :
    denoteN st.ns (ld.nameAt pk i) = some (ldC.nameAt i) := by
  simp only [ConRon.Arena.Frontend.Olean.HeaderLoads.nameAt,
    ConLeche.Frontend.Olean.HeaderLoads.nameAt]
  have := listRel_getElem? hl.order i
  simp only [Array.getElem?_toList] at this
  revert this
  generalize ld.order[i]? = a
  generalize ldC.order[i]? = b
  intro h
  cases h with
  | none => exact hn.anon
  | some h => exact h

/-- One clash's copies, by module name, read back. -/
theorem clashCopiesRow_rel {st : EStore} {pk : ConRon.Arena.Frontend.Olean.OleanPins}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (hn : NullsRel st pk) (hl : LoadsRel st ld ldC) :
    ∀ {cs : List (Copy × ConRon.Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit)}
      {csC : List (Copy × ConstantVal × CKindF ConLeche.Name Unit)},
      ListRel (CopyInfoRel st) cs csC →
      ListRel (fun (x : NIdx × ConRon.Arena.Frontend.Olean.StmtRec) (y : ConLeche.Name × ConstantVal) =>
          denoteN st.ns x.1 = some y.1 ∧ denoteStmt st x.2 = some y.2)
        (cs.map fun (cp, cv, _) => (ld.nameAt pk cp.mod, cv))
        (csC.map fun (cp, cv, _) => (ldC.nameAt cp.mod, cv))
  | _, _, .nil => .nil
  | _, _, .cons (a := (cp, cv, k)) (b := (cp', cv', k')) ⟨h1, h2, _⟩ t => by
    simp only at h1
    subst h1
    exact .cons ⟨nameAt_rel hn hl cp.mod, h2⟩ (clashCopiesRow_rel hn hl t)

/-- con-leche: ConLeche/Driver/Reach.lean:778-782 clashCopiesOf — **the copies of every name
two loaded modules hold, by name, read back**: a map over handles against one over names, each
row's copies the module names and statements denoted. -/
theorem clashCopiesOf_rel {st : EStore} (hw : NStoreWF st.ns)
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} (hn : NullsRel st pk)
    {wr : ConRon.Arena.Frontend.Olean.WorkerReads} {wrC : ConLeche.Frontend.Olean.WorkerReads}
    (hwr : WorkerReadsRel st wr wrC) :
    HMRel (fun (a : Array (NIdx × ConRon.Arena.Frontend.Olean.StmtRec))
        (b : Array (ConLeche.Name × ConstantVal)) =>
        ListRel (fun x y => denoteN st.ns x.1 = some y.1 ∧ denoteStmt st x.2 = some y.2)
          a.toList b.toList) st
      (ConRon.Arena.Modular.clashCopiesOf pk wr) (ConLeche.Driver.clashCopiesOf wrC) := by
  unfold ConRon.Arena.Modular.clashCopiesOf ConLeche.Driver.clashCopiesOf
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  have key : ∀ (l : List ConRon.Arena.Frontend.Olean.Clash) (lC : List ConLeche.Frontend.Olean.Clash)
      (M : Std.HashMap NIdx (Array (NIdx × ConRon.Arena.Frontend.Olean.StmtRec)))
      (MC : Std.HashMap ConLeche.Name (Array (ConLeche.Name × ConstantVal))),
      ListRel (ClashRel st) l lC →
      HMRel (fun (a : Array (NIdx × ConRon.Arena.Frontend.Olean.StmtRec))
        (b : Array (ConLeche.Name × ConstantVal)) =>
        ListRel (fun x y => denoteN st.ns x.1 = some y.1 ∧ denoteStmt st x.2 = some y.2)
          a.toList b.toList) st M MC →
      HMRel (fun (a : Array (NIdx × ConRon.Arena.Frontend.Olean.StmtRec))
        (b : Array (ConLeche.Name × ConstantVal)) =>
        ListRel (fun x y => denoteN st.ns x.1 = some y.1 ∧ denoteStmt st x.2 = some y.2)
          a.toList b.toList) st
        (l.foldl (fun m cl => m.insert cl.name
          (cl.copies.map fun (cp, cv, _) => (wr.loads.nameAt pk cp.mod, cv))) M)
        (lC.foldl (fun m cl => m.insert cl.name
          (cl.copies.map fun (cp, cv, _) => (wrC.loads.nameAt cp.mod, cv))) MC) := by
    intro l lC M MC hl hM
    induction hl generalizing M MC with
    | nil => exact hM
    | cons hc _ ih =>
      apply ih
      refine hM.insert hw hc.name ?_
      simpa [Array.toList_map] using clashCopiesRow_rel hn hwr.loads hc.copies
  exact key _ _ {} {} hwr.clashes (HMRel.empty _ _)

end ConRon.Bridge.Modular
