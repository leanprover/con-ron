/-
# `ConRon.Bridge.Inductives.BlockParts` — Theorem 1 for the block recogniser

`Arena/Inductives/BlockParts.lean`'s twins against
`ConLeche/Kernel/Inductives/BlockParts.lean` (task #105): the record's
projections, `withSort`, `complete`, the split, the per-member readers
(`recTargetOf`, `blockCounts?`, `ctorMember?`, `blockGroups`), the recursor
records' pins (`blockRecLpsOk`, `blockRecNameSetOk`,
`blockRecNamesUnreserved`) and the recogniser (`blockMemberCounts?`,
`blockShape?`, `blockParts?`).

**Grades.**  The projections, the split and the level pin are pure on both
sides and their statements are plain equations.  The readers are `PSpec`
(they intern and read, nothing more); `blockRecNamesUnreserved` reads the pin
table (`PSpecP`); `withSort`, `blockShape?` and `blockParts?` ask `lvlEq?` for
`isProp`, whose cached verdict is the denotation only under `CheckOK` — so
they are `CSpec`, the old `withSort_spec`/`nativeShape?_spec` argument.

**`blockParts?_spec` is TWO-SIDED** (`ROp`): the dispatch between
`checkBlock` and `checkShapeless` reads it and nothing else.
-/
import ConRon.Bridge.Inductives.StructParts
import ConRon.Bridge.Inductives.PosWalks

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## `Option`'s `mapM`, the record lists' shape -/

/-- con-leche: none — `Option`'s `mapM` at a cons, inverted. -/
theorem mapM_option_cons_inv {α β : Type} {f : α → Option β} {x : α} {xs : List α}
    {ys : List β} (h : (x :: xs).mapM f = some ys) :
    ∃ y ys', ys = y :: ys' ∧ f x = some y ∧ xs.mapM f = some ys' := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
  cases hx : f x with
  | none => rw [hx] at h; simp at h
  | some y =>
    rw [hx] at h
    cases hxs : xs.mapM f with
    | none => rw [hxs] at h; simp at h
    | some zs =>
      rw [hxs] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      exact ⟨y, zs, h.symm, rfl, rfl⟩

/-- con-leche: none — and built back up. -/
theorem mapM_option_cons {α β : Type} {f : α → Option β} {x : α} {xs : List α}
    {y : β} {ys : List β} (hx : f x = some y) (hxs : xs.mapM f = some ys) :
    (x :: xs).mapM f = some (y :: ys) := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, hx, hxs,
    Option.bind_some]

/-- con-leche: none — `Option`'s `mapM` at an index. -/
theorem mapM_option_getElem?_bind {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ (j : Nat),
      ys[j]? = xs[j]?.bind f := by
  intro xs
  induction xs with
  | nil =>
    intro ys h j
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons x xs ih =>
    intro ys h j
    obtain ⟨y, ys', rfl, hx, hxs⟩ := mapM_option_cons_inv h
    cases j with
    | zero => simp [hx]
    | succ j => simpa using ih hxs j

/-- con-leche: none — `Option`'s `mapM` of a `map`. -/
theorem mapM_option_map {α β γ : Type} {f : β → Option γ} {g : α → β} (xs : List α) :
    (xs.map g).mapM f = xs.mapM (fun x => f (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.mapM_cons, ih]

/-- con-leche: none — `Option`'s `mapM` is a `map` when every image is
`some`. -/
theorem mapM_option_eq_map {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ (xs : List α), (∀ x ∈ xs, f x = some (g x)) → xs.mapM f = some (xs.map g) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    exact mapM_option_cons (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

/-! ## The record's projections -/

/-- con-leche: none — `dShape`, inverted. -/
theorem dShape_inv {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) :
    ∃ ms rs el s, p.members.mapM (dMember st) = some ms ∧
      p.recs.mapM (dRec st) = some rs ∧ denoteN st.ns p.elim = some el ∧
      denoteL st.ls p.resSort = some s ∧
      pP = ⟨ms, rs, p.nP, el, s, p.large, p.isProp⟩ := by
  simp only [dShape] at h
  cases h1 : p.members.mapM (dMember st) with
  | none => rw [h1] at h; exact nomatch h
  | some ms =>
  cases h2 : p.recs.mapM (dRec st) with
  | none => rw [h1, h2] at h; exact nomatch h
  | some rs =>
  cases h3 : denoteN st.ns p.elim with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some el =>
  cases h4 : denoteL st.ls p.resSort with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some s =>
  rw [h1, h2, h3, h4] at h
  exact ⟨ms, rs, el, s, rfl, rfl, rfl, rfl, (Option.some.inj h).symm⟩

/-- con-leche: none — `dMember`, inverted. -/
theorem dMember_inv {st : EStore} {m : Arena.MemberShape} {mP : ConLeche.MemberShape}
    (h : dMember st m = some mP) :
    ∃ cv cs, Frontend.denoteCV st m.cvT = some cv ∧ dCtors st m.ctors = some cs ∧
      mP = ⟨cv, m.nIdx, cs⟩ := by
  simp only [dMember] at h
  cases h1 : Frontend.denoteCV st m.cvT with
  | none => rw [h1] at h; exact nomatch h
  | some cv =>
  cases h2 : dCtors st m.ctors with
  | none => rw [h1, h2] at h; exact nomatch h
  | some cs =>
  rw [h1, h2] at h
  exact ⟨cv, cs, rfl, rfl, (Option.some.inj h).symm⟩

/-- con-leche: none — `dRec`, inverted. -/
theorem dRec_inv {st : EStore} {r : Arena.RecShape} {rP : ConLeche.RecShape}
    (h : dRec st r = some rP) :
    ∃ cv rhss, Frontend.denoteCV st r.cvR = some cv ∧
      Frontend.denoteEList st r.rhss = some rhss ∧
      rP = ⟨cv, r.rP, r.mI, r.tgt, rhss⟩ := by
  simp only [dRec] at h
  cases h1 : Frontend.denoteCV st r.cvR with
  | none => rw [h1] at h; exact nomatch h
  | some cv =>
  cases h2 : Frontend.denoteEList st r.rhss with
  | none => rw [h1, h2] at h; exact nomatch h
  | some rhss =>
  rw [h1, h2] at h
  exact ⟨cv, rhss, rfl, rfl, (Option.some.inj h).symm⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:123-127 numCtorsOf —
the constructor count survives the denotation. -/
theorem numCtorsOf_spec {st : EStore} :
    ∀ {ms : List Arena.MemberShape} {msP : List ConLeche.MemberShape},
      ms.mapM (dMember st) = some msP → Arena.numCtorsOf ms = ConLeche.numCtorsOf msP := by
  intro ms
  induction ms with
  | nil =>
    intro msP h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons m ms ih =>
    intro msP h
    obtain ⟨mP, msP', rfl, hm, hms⟩ := mapM_option_cons_inv h
    obtain ⟨cv, cs, -, hcs, rfl⟩ := dMember_inv hm
    simp only [Arena.numCtorsOf, ConLeche.numCtorsOf, ih hms,
      mapM_option_length (f := dCtor st) hcs]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:131-132 BlockShape.k -/
theorem BlockShape.k_spec {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) : p.k = pP.k := by
  obtain ⟨ms, rs, el, s, hms, -, -, -, rfl⟩ := dShape_inv h
  simp only [Arena.BlockShape.k, ConLeche.BlockShape.k, mapM_option_length hms]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:133-134 BlockShape.numCtors -/
theorem BlockShape.numCtors_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    p.numCtors = pP.numCtors := by
  obtain ⟨ms, rs, el, s, hms, -, -, -, rfl⟩ := dShape_inv h
  exact numCtorsOf_spec hms

/-- con-leche: none — the member names, over the member list. -/
theorem memberNames_go {st : EStore} :
    ∀ {ms : List Arena.MemberShape} {msP : List ConLeche.MemberShape},
      ms.mapM (dMember st) = some msP →
      Frontend.denoteNList st.ns (ms.map (·.cvT.name)) = some (msP.map (·.cvT.name)) := by
  intro ms
  induction ms with
  | nil =>
    intro msP h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons m ms ih =>
    intro msP h
    obtain ⟨mP, msP', rfl, hm, hms⟩ := mapM_option_cons_inv h
    obtain ⟨cv, cs, hcv, -, rfl⟩ := dMember_inv hm
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hcv, ih hms]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:137-138 BlockShape.memberNames
— the twin's name-handle list denotes con-leche's names. -/
theorem BlockShape.memberNames_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    Frontend.denoteNList st.ns p.memberNames = some pP.memberNames := by
  obtain ⟨ms, rs, el, s, hms, -, -, -, rfl⟩ := dShape_inv h
  exact memberNames_go hms

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:139-140 BlockShape.nIdxs -/
theorem BlockShape.nIdxs_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) : p.nIdxs = pP.nIdxs := by
  obtain ⟨ms, rs, el, s, hms, -, -, -, rfl⟩ := dShape_inv h
  simp only [Arena.BlockShape.nIdxs, ConLeche.BlockShape.nIdxs]
  clear h
  generalize p.members = xs at hms
  induction xs generalizing ms with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms; rfl
  | cons m xs ih =>
    obtain ⟨mP, msP', rfl, hm, hxs⟩ := mapM_option_cons_inv hms
    obtain ⟨cv, cs, -, -, rfl⟩ := dMember_inv hm
    simp only [List.map_cons, ih msP' hxs]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:141-144 BlockShape.lps -/
theorem BlockShape.lps_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    Frontend.denoteNList st.ns p.lps = some pP.lps := by
  obtain ⟨ms, rs, el, s, hms, -, -, -, rfl⟩ := dShape_inv h
  simp only [Arena.BlockShape.lps, ConLeche.BlockShape.lps]
  cases hm : p.members with
  | nil =>
    rw [hm] at hms
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms; rfl
  | cons m xs =>
    rw [hm] at hms
    obtain ⟨mP, msP', rfl, hm, -⟩ := mapM_option_cons_inv hms
    obtain ⟨cv, cs, hcv, -, rfl⟩ := dMember_inv hm
    simpa using denoteCV_lps hcv

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:145-147 BlockShape.allCtors -/
theorem BlockShape.allCtors_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    dCtors st p.allCtors = some pP.allCtors := by
  obtain ⟨ms, rs, el, s, hms, -, -, -, rfl⟩ := dShape_inv h
  simp only [Arena.BlockShape.allCtors, ConLeche.BlockShape.allCtors]
  clear h
  generalize p.members = xs at hms
  induction xs generalizing ms with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms; rfl
  | cons m xs ih =>
    obtain ⟨mP, msP', rfl, hm, hxs⟩ := mapM_option_cons_inv hms
    obtain ⟨cv, cs, -, hcs, rfl⟩ := dMember_inv hm
    have h2 := ih msP' hxs
    simp only [dCtors] at h2 hcs ⊢
    simp only [List.map_cons, List.flatten_cons, List.mapM_append, hcs, h2,
      Option.bind_eq_bind, Option.pure_def, Option.bind_some]

/-- con-leche: none — the recursor records at an index, read at their two
counts. -/
theorem recs_getElem?_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) (r : Nat) :
    (p.recs[r]?).map (fun rc => (rc.rP, rc.mI)) =
      (pP.recs[r]?).map (fun rc => (rc.rP, rc.mI)) := by
  obtain ⟨ms, rs, el, s, -, hrs, -, -, rfl⟩ := dShape_inv h
  have hg := mapM_option_getElem?_bind hrs r
  show _ = (rs[r]?).map _
  rw [hg]
  cases hr : p.recs[r]? with
  | none => rfl
  | some rc =>
    simp only [Option.bind_some]
    cases hd : dRec st rc with
    | none =>
      exfalso
      rw [hr] at hg
      change rs[r]? = dRec st rc at hg
      rw [hd] at hg
      have h1 := List.getElem?_eq_none_iff.mp hg
      obtain ⟨h2, -⟩ := List.getElem?_eq_some_iff.mp hr
      have hl := mapM_option_length hrs
      omega
    | some rcP =>
      obtain ⟨cv, rhss, -, -, rfl⟩ := dRec_inv hd
      rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:154-160 BlockShape.rulePrefixAt -/
theorem BlockShape.rulePrefixAt_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) (r : Nat) :
    p.rulePrefixAt r = pP.rulePrefixAt r := by
  have e := recs_getElem?_spec h r
  simp only [Arena.BlockShape.rulePrefixAt, ConLeche.BlockShape.rulePrefixAt,
    List.getD_eq_getElem?_getD]
  cases h1 : p.recs[r]? <;> cases h2 : pP.recs[r]? <;> rw [h1, h2] at e <;>
    simp_all <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:162-165 BlockShape.majorIdxAt -/
theorem BlockShape.majorIdxAt_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) (r : Nat) :
    p.majorIdxAt r = pP.majorIdxAt r := by
  have e := recs_getElem?_spec h r
  simp only [Arena.BlockShape.majorIdxAt, ConLeche.BlockShape.majorIdxAt,
    List.getD_eq_getElem?_getD]
  cases h1 : p.recs[r]? <;> cases h2 : pP.recs[r]? <;> rw [h1, h2] at e <;>
    simp_all <;> rfl

/-! ## `withSort` and `complete` -/

/-- con-leche: none — the twin's three-way `match` on `lvlEq?`'s verdict is
con-leche's `== some true`. -/
theorem isProp_match_eq (v : Option Bool) :
    (match v with
      | some true => true
      | some false => false
      | none => false) = (v == some true) := by
  rcases v with _ | _ | _ <;> rfl

/-- con-leche: none — **`isProp`, read off `lvlEq? y zeroLevel`**: the
verdict is `Level.isEquiv sP .zero` under `CheckOK` (the cache licence),
carried along the pure steps before the call. -/
theorem lvlEqZero_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {s₀ s s₁ s' : AState} {y z : LIdx} {sP : Level} {v : Option Bool}
    (hc : CheckOK μ env fe s₀) (q : PStep s₀ s) (hy : denoteL s.store.ls y = some sP)
    (hz : Arena.zeroLevel s = .ok (z, s₁)) (hr : Arena.lvlEq? y z s₁ = .ok (v, s')) :
    PStep s₀ s' ∧ v = Level.isEquiv sP .zero := by
  obtain ⟨rfl, hzl⟩ := zeroLevel_run (hc.pins.mono q.ext q.pins) hz
  have hcY := (q.toCore hc).ok
  obtain ⟨-, -, -, lu, lv, hlu, hlv, ha⟩ :=
    AM.of_run (P := fun t => t = s₁) rfl hr (Core.lvlEq?_spec s₁ y z hcY)
  rw [hy] at hlu; rw [hzl] at hlv
  cases hlu; cases hlv
  exact ⟨q.trans (lvlEq?_pstep q.ok hr), ha⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:167-171 BlockShape.withSort
The record completed with the former stage's result sort.  **CORE grade**:
`isProp` is `lvlEq?`'s verdict, the denotation only under `CheckOK` (the old
tier's `withSort_spec` argument). -/
theorem BlockShape.withSort_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (s : LIdx) (sP : Level) :
    CSpec μ env fe (fun st => dShape st p = some pP ∧ denoteL st.ls s = some sP)
      (Arena.BlockShape.withSort p s)
      (fun st r => dShape st r = some (pP.withSort sP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hp, hs⟩ := hpre
  simp only [Arena.BlockShape.withSort] at hrun
  obtain ⟨z, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨a, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨q, ha⟩ := lvlEqZero_run hok (PStep.refl hok.state) hs h1 h3
  obtain ⟨rfl, rfl⟩ := pureOk h4
  refine ⟨q.toCore hok, ?_⟩
  obtain ⟨ms, rs, el, sl, hms, hrs, hel, -, rfl⟩ := dShape_inv (dShape_ext q.ext _ _ hp)
  simp only [dShape, hms, hrs, hel, denoteL_ext hs q.ext, ha,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [ConLeche.BlockShape.withSort]
  generalize Level.isEquiv sP Level.zero = v
  rcases v with _ | _ | _ <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:203-206 BlockParts.complete
— pure on both sides. -/
theorem BlockParts.complete_spec {st : EStore} {p₀ : Arena.BlockParts}
    {q₀ : ConLeche.BlockParts} {p₁ : Arena.BlockShape} {q₁ : ConLeche.BlockShape}
    (_h₀ : dParts st p₀ = some q₀) (h₁ : dShape st p₁ = some q₁) :
    dParts st (p₀.complete p₁) = some (q₀.complete q₁) := by
  simp only [dParts, Arena.BlockParts.complete, ConLeche.BlockParts.complete, h₁,
    Option.map_some]

/-! ## The split -/

/-- con-leche: none — a recursor's four-tuple, as `blockSplitRecs` answers
it, denotes. -/
def dRec4 (st : EStore) (r : IConstantVal × Nat × Nat × List IRecRule) :
    Option (ConstantVal × Nat × Nat × List RecRule) := do
  let cv ← Frontend.denoteCV st r.1
  let rules ← Frontend.denoteRules st r.2.2.2
  pure (cv, r.2.1, r.2.2.1, rules)

theorem dRec4_ext : DExt dRec4 := by
  intro st st' hx r y h
  simp only [dRec4, Option.bind_eq_bind, Option.pure_def] at h ⊢
  cases h1 : Frontend.denoteCV st r.1 with
  | none => rw [h1] at h; exact nomatch h
  | some cv =>
  cases h2 : Frontend.denoteRules st r.2.2.2 with
  | none => rw [h1, h2] at h; exact nomatch h
  | some rules =>
  rw [h1, h2] at h
  rw [denoteCV_ext h1 hx, denoteRules_ext hx _ _ h2]
  exact h

/-- con-leche: none — `dRec4`, inverted. -/
theorem dRec4_inv {st : EStore} {r : IConstantVal × Nat × Nat × List IRecRule}
    {q : ConstantVal × Nat × Nat × List RecRule} (h : dRec4 st r = some q) :
    Frontend.denoteCV st r.1 = some q.1 ∧ r.2.1 = q.2.1 ∧ r.2.2.1 = q.2.2.1 ∧
      Frontend.denoteRules st r.2.2.2 = some q.2.2.2 := by
  simp only [dRec4, Option.bind_eq_bind, Option.pure_def] at h
  cases h1 : Frontend.denoteCV st r.1 with
  | none => rw [h1] at h; exact nomatch h
  | some cv =>
  cases h2 : Frontend.denoteRules st r.2.2.2 with
  | none => rw [h1, h2] at h; exact nomatch h
  | some rules =>
  rw [h1, h2] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- con-leche: none — `denoteCIList` at a cons, inverted. -/
theorem denoteCIList_cons_inv {st : EStore} {c : IConstantInfo} {cs : List IConstantInfo}
    {xs : List ConstantInfo} (h : Frontend.denoteCIList st (c :: cs) = some xs) :
    ∃ x xs', xs = x :: xs' ∧ Frontend.denoteCI st c = some x ∧
      Frontend.denoteCIList st cs = some xs' := by
  simp only [Frontend.denoteCIList] at h
  cases hc : Frontend.denoteCI st c with
  | none => rw [hc] at h; simp at h
  | some x =>
    cases hcs : Frontend.denoteCIList st cs with
    | none => rw [hc, hcs] at h; simp at h
    | some xs' =>
      rw [hc, hcs] at h
      exact ⟨x, xs', (Option.some.inj h).symm, rfl, rfl⟩

/-- con-leche: none — **`denoteCI` keeps the constant's kind**, with the
three kinds the split reads carried field by field. -/
def CIShape (st : EStore) : IConstantInfo → ConstantInfo → Prop
  | .axiomInfo _, .axiomInfo _ => True
  | .defnInfo _ _ _, .defnInfo _ _ _ => True
  | .thmInfo _ _, .thmInfo _ _ => True
  | .indInfo v _, .indInfo cv _ => Frontend.denoteCV st v = some cv
  | .ctorInfo v a b, .ctorInfo cv a' b' => Frontend.denoteCV st v = some cv ∧ a = a' ∧ b = b'
  | .recInfo v a b rs, .recInfo cv a' b' rs' =>
    Frontend.denoteCV st v = some cv ∧ a = a' ∧ b = b' ∧ Frontend.denoteRules st rs = some rs'
  | .projInfo _, .projInfo _ => True
  | _, _ => False

theorem denoteCI_shape {st : EStore} {c : IConstantInfo} {x : ConstantInfo}
    (h : Frontend.denoteCI st c = some x) : CIShape st c x := by
  cases c with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, _, rfl⟩ := h; trivial
  | defnInfo v e hint =>
    simp only [Frontend.denoteCI] at h
    split at h
    · obtain rfl := Option.some.inj h; trivial
    · exact nomatch h
  | thmInfo v e =>
    simp only [Frontend.denoteCI] at h
    split at h
    · obtain rfl := Option.some.inj h; trivial
    · exact nomatch h
  | indInfo v caps =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv _ hcv _
      obtain rfl := Option.some.inj h; exact hcv
    · exact nomatch h
  | ctorInfo v a b =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h; exact ⟨hcv, rfl, rfl⟩
  | recInfo v a b rs =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv rules hcv hr
      obtain rfl := Option.some.inj h; exact ⟨hcv, rfl, rfl, hr⟩
    · exact nomatch h
  | projInfo t =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨pt, _, rfl⟩ := h; trivial

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:231-237 blockSplitRecs
The closing recursors, two-sided. -/
theorem blockSplitRecs_spec (st : EStore) :
    ∀ (block : List IConstantInfo) (blockP : List ConstantInfo),
      Frontend.denoteCIList st block = some blockP →
      ROp (fun q st r => r.mapM (dRec4 st) = some q) (ConLeche.blockSplitRecs blockP) st
        (Arena.blockSplitRecs block) := by
  intro block
  induction block with
  | nil =>
    intro blockP h
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl⟩
  | cons c cs ih =>
    intro blockP h
    obtain ⟨x, xs, rfl, hc, hcs⟩ := denoteCIList_cons_inv h
    have hsh := denoteCI_shape hc
    cases c <;> cases x <;> (try exact hsh.elim) <;> (try rfl)
    rename_i v mI rP rs cv mI' rP' rs'
    obtain ⟨hv, rfl, rfl, hr⟩ := hsh
    have hih := ih xs hcs
    simp only [Arena.blockSplitRecs, ConLeche.blockSplitRecs]
    cases ha : Arena.blockSplitRecs cs with
    | none =>
      rw [ha] at hih
      simp only [ROp] at hih
      simp only [hih, Option.map_none]
      rfl
    | some a =>
      rw [ha] at hih
      obtain ⟨b, hb, hrel⟩ := hih
      simp only [hb, Option.map_some]
      refine ⟨_, rfl, mapM_option_cons ?_ hrel⟩
      simp only [dRec4, hv, hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:239-244 blockSplitCtors
The constructors, then the recursors, two-sided. -/
theorem blockSplitCtors_spec (st : EStore) :
    ∀ (block : List IConstantInfo) (blockP : List ConstantInfo),
      Frontend.denoteCIList st block = some blockP →
      ROp (fun q st r => denoteCtors3 st r.1 = some q.1 ∧ r.2.mapM (dRec4 st) = some q.2)
        (ConLeche.blockSplitCtors blockP) st (Arena.blockSplitCtors block) := by
  intro block
  induction block with
  | nil =>
    intro blockP h
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h
    exact ⟨([], []), rfl, rfl, rfl⟩
  | cons c cs ih =>
    intro blockP h
    have hR := blockSplitRecs_spec st _ _ h
    obtain ⟨x, xs, rfl, hc, hcs⟩ := denoteCIList_cons_inv h
    have hsh := denoteCI_shape hc
    by_cases hk : ∃ v a b, c = .ctorInfo v a b
    · obtain ⟨v, a, b, rfl⟩ := hk
      cases x <;> (try exact hsh.elim)
      rename_i cv a' b'
      obtain ⟨hv, rfl, rfl⟩ := hsh
      have hih := ih xs hcs
      simp only [Arena.blockSplitCtors, ConLeche.blockSplitCtors]
      cases ha : Arena.blockSplitCtors cs with
      | none =>
        rw [ha] at hih
        simp only [ROp] at hih
        simp only [hih, Option.map_none]
        rfl
      | some a =>
        rw [ha] at hih
        obtain ⟨b, hb, h1, h2⟩ := hih
        simp only [hb, Option.map_some]
        refine ⟨_, rfl, ?_, h2⟩
        simp only [denoteCtors3, hv, h1]
    · have e1 : Arena.blockSplitCtors (c :: cs) =
          (match Arena.blockSplitRecs (c :: cs) with
           | some rs => some ([], rs)
           | none => none) := by
        cases c <;> first | rfl | exact absurd ⟨_, _, _, rfl⟩ hk
      have e2 : ConLeche.blockSplitCtors (x :: xs) =
          (ConLeche.blockSplitRecs (x :: xs)).map fun rs => ([], rs) := by
        cases c <;> cases x <;> (try exact hsh.elim) <;> first | rfl | exact absurd ⟨_, _, _, rfl⟩ hk
      rw [e1, e2]
      cases ha : Arena.blockSplitRecs (c :: cs) with
      | none =>
        rw [ha] at hR
        simp only [ROp] at hR
        simp only [hR, Option.map_none]
        rfl
      | some a =>
        rw [ha] at hR
        obtain ⟨b, hb, h1⟩ := hR
        simp only [hb, Option.map_some]
        exact ⟨_, rfl, rfl, h1⟩

/-- con-leche: none — the split's answer denotes: the formers, the
constructors with their two counts, the recursors' four-tuples. -/
def RSplit (q : List ConstantVal × List (ConstantVal × Nat × Nat) ×
      List (ConstantVal × Nat × Nat × List RecRule)) (st : EStore)
    (r : List IConstantVal × List (IConstantVal × Nat × Nat) ×
      List (IConstantVal × Nat × Nat × List IRecRule)) : Prop :=
  r.1.mapM (Frontend.denoteCV st) = some q.1 ∧ denoteCtors3 st r.2.1 = some q.2.1 ∧
    r.2.2.mapM (dRec4 st) = some q.2.2

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:246-252 blockSplit
The type formers, the constructors and the recursors, two-sided. -/
theorem blockSplit_spec (st : EStore) :
    ∀ (block : List IConstantInfo) (blockP : List ConstantInfo),
      Frontend.denoteCIList st block = some blockP →
      ROp RSplit (ConLeche.blockSplit blockP) st (Arena.blockSplit block) := by
  intro block
  induction block with
  | nil =>
    intro blockP h
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h
    exact ⟨([], [], []), rfl, rfl, rfl, rfl⟩
  | cons c cs ih =>
    intro blockP h
    have hC := blockSplitCtors_spec st _ _ h
    obtain ⟨x, xs, rfl, hc, hcs⟩ := denoteCIList_cons_inv h
    have hsh := denoteCI_shape hc
    by_cases hk : ∃ v caps, c = .indInfo v caps
    · obtain ⟨v, caps, rfl⟩ := hk
      cases x <;> (try exact hsh.elim)
      rename_i cv caps'
      have hih := ih xs hcs
      simp only [Arena.blockSplit, ConLeche.blockSplit]
      cases ha : Arena.blockSplit cs with
      | none =>
        rw [ha] at hih
        simp only [ROp] at hih
        simp only [hih, Option.map_none]
        rfl
      | some a =>
        rw [ha] at hih
        obtain ⟨b, hb, h1, h2, h3⟩ := hih
        simp only [hb, Option.map_some]
        exact ⟨_, rfl, mapM_option_cons hsh h1, h2, h3⟩
    · have e1 : Arena.blockSplit (c :: cs) =
          (match Arena.blockSplitCtors (c :: cs) with
           | some q => some ([], q.1, q.2)
           | none => none) := by
        cases c <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hk
      have e2 : ConLeche.blockSplit (x :: xs) =
          (ConLeche.blockSplitCtors (x :: xs)).map fun q => ([], q.1, q.2) := by
        cases c <;> cases x <;> (try exact hsh.elim) <;> first | rfl | exact absurd ⟨_, _, rfl⟩ hk
      rw [e1, e2]
      cases ha : Arena.blockSplitCtors (c :: cs) with
      | none =>
        rw [ha] at hC
        simp only [ROp] at hC
        simp only [hC, Option.map_none]
        rfl
      | some a =>
        rw [ha] at hC
        obtain ⟨b, hb, h1, h2⟩ := hC
        simp only [hb, Option.map_some]
        exact ⟨_, rfl, rfl, h1, h2⟩

end ConRon.Bridge.Inductives
