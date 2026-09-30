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
import ConRon.Bridge.Inductives.FieldTele

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

/-! ## The per-member readers -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:254-271 recTargetOf
The member a recursor's MAJOR names: `stripPis`, the `forallE` view, the head
through `getAppFn`, the name through `findIdx_handle_eq`. -/
theorem recTargetOf_spec (names : List NIdx) (namesP : List ConLeche.Name) (mI : Nat)
    (ty : EIdx) (tyP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteE st ty = some tyP)
      (Arena.recTargetOf names mI ty) (RV (ConLeche.recTargetOf namesP mI tyP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hN, hd⟩ := hp
  have hlen := PW.denoteNList_length hN
  simp only [Arena.recTargetOf] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hd h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨PStep.refl hok, ?_⟩
    show names.length = _
    simp only [ConLeche.recTargetOf, stripPis_none hbp, hlen]
  | some q =>
    obtain ⟨bs, e⟩ := q
    obtain ⟨xs, x, hsp, hx⟩ := stripPis_some hbp
    dsimp only at h2
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [if_pos htg] at h2
      obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨rfl, ho⟩ := PW.viewBind_run h3
      cases o with
      | none => exact absurd h4 (fun hc => PW.failDanglingE_ok hc)
      | some p =>
        obtain ⟨d, b, m⟩ := p
        have hw := view_of_viewBind_tag_forallE htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, -⟩ := denote_forallE_inv hok.wf hw hx
        dsimp only at h4
        obtain ⟨hh, s₃, h5, h6⟩ := bindOk h4
        obtain ⟨rfl, hhd⟩ := getAppFn_run hok hdd h5
        by_cases htc : (hh.tag == ETag.const) = true
        · rw [if_pos htc] at h6
          obtain ⟨o, s₄, h7, h8⟩ := bindOk h6
          obtain ⟨rfl, ho2⟩ := PW.viewConst_run h7
          cases o with
          | none => exact absurd h8 (fun hc => PW.failDanglingE_ok hc)
          | some p =>
            obtain ⟨n, us⟩ := p
            have hw2 := view_of_viewConst_tag htc ho2.symm
            obtain ⟨nm, ls, hc, hn, -⟩ := denote_const_inv hok.wf hw2 hhd
            dsimp only at h8
            have hf := PW.findIdx_handle_eq hok.wf hn hN
            cases hfi : names.findIdx? (· == n) with
            | none =>
              rw [hfi] at h8
              obtain ⟨rfl, rfl⟩ := pureOk h8
              refine ⟨PStep.refl hok, ?_⟩
              show names.length = _
              simp only [ConLeche.recTargetOf, hsp, hc]
              rw [← hf, ← hlen, hfi]
              rfl
            | some t =>
              rw [hfi] at h8
              obtain ⟨rfl, rfl⟩ := pureOk h8
              refine ⟨PStep.refl hok, ?_⟩
              show _ = ConLeche.recTargetOf namesP mI tyP
              simp only [ConLeche.recTargetOf, hsp, hc]
              rw [← hf, hfi]
              rfl
        · rw [if_neg htc] at h6
          obtain ⟨rfl, rfl⟩ := pureOk h6
          refine ⟨PStep.refl hok, ?_⟩
          show names.length = _
          simp only [ConLeche.recTargetOf, hsp]
          rw [hlen]
          generalize hg : dP.getAppFn = g at hhd
          cases g with
          | const c us => exact absurd (PW.tag_const_of_denote hok.wf hhd) (by simpa using htc)
          | _ => rfl
    · rw [if_neg htg] at h2
      obtain ⟨rfl, rfl⟩ := pureOk h2
      refine ⟨PStep.refl hok, ?_⟩
      show names.length = _
      simp only [ConLeche.recTargetOf, hsp]
      rw [hlen]
      cases x with
      | forallE d b m => exact absurd (PW.tag_forallE_of_denote hok.wf hx) (by simpa using htg)
      | _ => rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:273-299 blockCounts?
— the non-sort tail: the recursor's argument sums. -/
def blockCountsTail (nPd k nC nR : Nat) : Option (Nat × Nat) → Option (Nat × Nat)
  | none => none
  | some (mI, rP) =>
    if rP < nC + k || mI < rP then none
    else if rP - (nC + k) == nPd then some (nPd, mI - rP)
    else if k < nR && nPd + nR + nC ≤ rP then some (nPd, mI - rP)
    else none

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:273-299 blockCounts?
— con-leche's `match` on the whole pair re-read as a match on the residual,
which is what the twin's `view` dispatch decides. -/
theorem blockCounts_eq (nPd k nC nR : Nat) (cvTP : ConstantVal) (r : Option (Nat × Nat)) :
    ConLeche.blockCounts? nPd k nC nR cvTP r =
      (match (cvTP.type.piBinders).2 with
       | .sort _ =>
         if nPd ≤ (cvTP.type.piBinders).1.length then
           some (nPd, (cvTP.type.piBinders).1.length - nPd) else none
       | _ => blockCountsTail nPd k nC nR r) := by
  simp only [ConLeche.blockCounts?]
  cases h : cvTP.type.piBinders with
  | mk bs body =>
    cases body <;> rcases r with _ | ⟨mI, rP⟩ <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:273-299 blockCounts?
One member's parameter and index counts: `piBinders_spec`, the ten-way `view`
dispatch at the residual, `denoteBinders_length` for the telescope's
length. -/
theorem blockCounts?_spec (nPd k nC nR : Nat) (cvT : IConstantVal) (cvTP : ConstantVal)
    (r : Option (Nat × Nat)) :
    PSpec (fun st => Frontend.denoteCV st cvT = some cvTP)
      (Arena.blockCounts? nPd k nC nR cvT r)
      (RV (ConLeche.blockCounts? nPd k nC nR cvTP r)) := by
  intro s₀ s' x hok hcv hrun
  simp only [Arena.blockCounts?] at hrun
  obtain ⟨q, s1, k1, hz1⟩ := bindOk hrun
  obtain ⟨p1, hbs, hbody⟩ :=
    piBinders_spec Arena.coreWalkFuel cvT.type cvTP.type s₀ s1 q hok
      (denoteCV_type hcv) k1
  obtain ⟨bs, res⟩ := q
  dsimp only at hz1 hbs hbody
  obtain ⟨v, s2, k2, hz2⟩ := bindOk hz1
  obtain ⟨hs2, hview⟩ := view_run k2
  rw [hs2] at hz2
  have hlen : bs.length = (cvTP.type.piBinders).1.length := denoteBinders_length hbs
  have hbv : denoteEView s1.store v = some (cvTP.type.piBinders).2 := by
    rw [← denoteE_view_eq p1.ok.wf hview]; exact hbody
  rw [blockCounts_eq]
  cases v
  case sort u =>
    obtain ⟨l, hEq, _⟩ := denote_sort_inv p1.ok.wf hview hbody
    dsimp only at hz2
    rw [hEq, ← hlen]
    split at hz2
    · obtain ⟨rfl, rfl⟩ := pureOk hz2
      exact ⟨p1, by simp_all⟩
    · obtain ⟨rfl, rfl⟩ := pureOk hz2
      exact ⟨p1, by simp_all⟩
  all_goals
    (have hns := ExprOps.denoteEView_not_sort hbv (by simp)
     have hm : (match (cvTP.type.piBinders).2 with
         | .sort _ =>
           if nPd ≤ (cvTP.type.piBinders).1.length then
             some (nPd, (cvTP.type.piBinders).1.length - nPd) else none
         | _ => blockCountsTail nPd k nC nR r) = blockCountsTail nPd k nC nR r := by
       generalize (cvTP.type.piBinders).2 = e at hns
       cases e <;> first | rfl | exact absurd rfl (hns _)
     rw [hm]
     dsimp only at hz2
     rcases r with _ | ⟨mI, rP⟩
     · obtain ⟨rfl, rfl⟩ := pureOk hz2
       exact ⟨p1, rfl⟩
     · dsimp only at hz2
       simp only [blockCountsTail]
       split at hz2
       · rename_i hc; obtain ⟨rfl, rfl⟩ := pureOk hz2; exact ⟨p1, by simp [hc]⟩
       · rename_i hc
         split at hz2
         · rename_i hc2; obtain ⟨rfl, rfl⟩ := pureOk hz2; exact ⟨p1, by simp [hc, hc2]⟩
         · rename_i hc2
           split at hz2
           · rename_i hc3; obtain ⟨rfl, rfl⟩ := pureOk hz2
             exact ⟨p1, by simp only [hc, hc2, hc3]; simp_all⟩
           · rename_i hc3; obtain ⟨rfl, rfl⟩ := pureOk hz2
             exact ⟨p1, by simp only [hc, hc2, hc3]; simp_all⟩)

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:301-308 ctorMember?
The member a constructor belongs to: `stripPis`, `getAppFn`, then
`memberIdxAt?_spec` at the block's interned level list. -/
theorem ctorMember?_spec (names : List NIdx) (namesP : List ConLeche.Name) (lvls : LsIdx)
    (lpsP : List ConLeche.Name) (nP : Nat) (c : IConstantVal × Nat)
    (cP : ConstantVal × Nat) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss lvls = some (lpsP.map Level.param) ∧ dCtor st c = some cP)
      (Arena.ctorMember? names lvls nP c) (RV (ConLeche.ctorMember? namesP lpsP nP cP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hN, hL, hc⟩ := hp
  simp only [dCtor, Option.map_eq_some_iff] at hc
  obtain ⟨cv, hcv, rfl⟩ := hc
  simp only [Arena.ctorMember?] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hs1, hbp⟩ := stripPis_pstep hok (denoteCV_type hcv) h1
  rw [hs1] at h2
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨PStep.refl hok, ?_⟩
    show none = _
    simp only [ConLeche.ctorMember?, stripPis_none hbp]
  | some q =>
    obtain ⟨bs, e⟩ := q
    obtain ⟨xs, x, hsp, hx⟩ := stripPis_some hbp
    dsimp only at h2
    obtain ⟨hh, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨hs2, hhd⟩ := getAppFn_run hok hx h3
    rw [hs2] at h4
    obtain ⟨p4, h5⟩ := memberIdxAt?_spec names namesP lvls _ hh _ s₀ s' r hok
      ⟨hN, hL, hhd⟩ h4
    refine ⟨p4, ?_⟩
    simp only [RV] at h5 ⊢
    rw [h5]
    simp only [ConLeche.ctorMember?, hsp]

/-- con-leche: none — `Option`'s `mapM` of a reversed list. -/
theorem mapM_option_reverse {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.reverse.mapM f = some ys.reverse := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
           subst h; rfl
  | cons x xs ih =>
    intro ys h
    obtain ⟨y, ys', rfl, hx, hxs⟩ := mapM_option_cons_inv h
    simp only [List.reverse_cons, List.mapM_append, ih hxs, List.mapM_cons, List.mapM_nil, hx,
      Option.bind_eq_bind, Option.pure_def, Option.bind_some]

/-- con-leche: none — **`List.filterM` of a pure-grade test** (the accumulator
form `List.filterAuxM`): the kept elements denote the pure `filter`, reversed
onto the accumulator. -/
theorem filterAuxM_pstep {α β : Type} (d : EStore → α → Option β) (hd : DExt d)
    (P : EStore → Prop) (hP : ∀ {st st' : EStore}, Ext st st' → P st → P st')
    (f : α → AM Bool) (g : β → Bool)
    (hf : ∀ (a : α) (aP : β) (s₀ s' : AState) (b : Bool), StateOK s₀ → P s₀.store →
      d s₀.store a = some aP → f a s₀ = .ok (b, s') → PStep s₀ s' ∧ b = g aP) :
    ∀ (xs : List α) (xsP : List β) (acc : List α) (accP : List β) (s₀ s' : AState)
      (r : List α), StateOK s₀ → P s₀.store → xs.mapM (d s₀.store) = some xsP →
      acc.mapM (d s₀.store) = some accP → List.filterAuxM f xs acc s₀ = .ok (r, s') →
      PStep s₀ s' ∧ r.mapM (d s'.store) = some ((xsP.filter g).reverse ++ accP) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP acc accP s₀ s' r hok _ hxs hacc hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hxs
    subst hxs
    simp only [List.filterAuxM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, by simpa using hacc⟩
  | cons a as ih =>
    intro xsP acc accP s₀ s' r hok hp hxs hacc hrun
    obtain ⟨aP, asP, rfl, ha, has⟩ := mapM_option_cons_inv hxs
    simp only [List.filterAuxM] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, rfl⟩ := hf a aP s₀ s₁ b hok hp ha h1
    have hacc' : (cond (g aP) (a :: acc) acc).mapM (d s₁.store) =
        some (cond (g aP) (aP :: accP) accP) := by
      cases g aP
      · exact mapM_option_ext (fun x y h => hd p1.ext x y h) _ _ hacc
      · exact mapM_option_cons (hd p1.ext _ _ ha)
          (mapM_option_ext (fun x y h => hd p1.ext x y h) _ _ hacc)
    obtain ⟨p2, hr⟩ := ih asP _ _ s₁ s' r p1.ok (hP p1.ext hp)
      (mapM_option_ext (fun x y h => hd p1.ext x y h) _ _ has) hacc' h2
    refine ⟨p1.trans p2, ?_⟩
    rw [hr]
    cases hg : g aP <;> simp [hg]

theorem filterM_pstep {α β : Type} (d : EStore → α → Option β) (hd : DExt d)
    (P : EStore → Prop) (hP : ∀ {st st' : EStore}, Ext st st' → P st → P st')
    (f : α → AM Bool) (g : β → Bool)
    (hf : ∀ (a : α) (aP : β) (s₀ s' : AState) (b : Bool), StateOK s₀ → P s₀.store →
      d s₀.store a = some aP → f a s₀ = .ok (b, s') → PStep s₀ s' ∧ b = g aP)
    (xs : List α) (xsP : List β) (s₀ s' : AState) (r : List α) (hok : StateOK s₀)
    (hp : P s₀.store) (hxs : xs.mapM (d s₀.store) = some xsP)
    (hrun : xs.filterM f s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r.mapM (d s'.store) = some (xsP.filter g) := by
  simp only [List.filterM] at hrun
  obtain ⟨as, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, has⟩ := filterAuxM_pstep d hd P hP f g hf xs xsP [] [] s₀ s₁ as hok hp hxs rfl h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  refine ⟨p1, ?_⟩
  simpa using mapM_option_reverse has

/-- con-leche: none — a pointwise `Option` relation is a `mapM`. -/
theorem ListRel.toMapM {β γ : Type} {d : EStore → β → Option γ} {st : EStore} :
    ∀ {bs : List β} {cs : List γ}, ListRel (fun st b c => d st b = some c) st bs cs →
      bs.mapM (d st) = some cs := by
  intro bs
  induction bs with
  | nil => intro cs h; cases cs with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons b bs ih =>
    intro cs h
    cases cs with
    | nil => exact h.elim
    | cons c cs => exact mapM_option_cons h.1 (ih h.2)

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:310-323 blockGroups
The constructors grouped by member: one `mapM` over the members, one `filterM`
over the constructors (`filterM_pstep`), `ctorMember?_spec` at each. -/
theorem blockGroups_spec (names : List NIdx) (namesP : List ConLeche.Name) (lvls : LsIdx)
    (lpsP : List ConLeche.Name) (nP k : Nat) (cs : List (IConstantVal × Nat))
    (csP : List (ConstantVal × Nat)) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss lvls = some (lpsP.map Level.param) ∧ dCtors st cs = some csP)
      (Arena.blockGroups names lvls nP k cs)
      (fun st r => r.mapM (dCtors st) = some (ConLeche.blockGroups namesP lpsP nP k csP)) := by
  intro s₀ s' r hok hp hrun
  simp only [Arena.blockGroups] at hrun
  simp only [ConLeche.blockGroups]
  have hPx : ∀ {st st' : EStore}, Ext st st' →
      (Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss lvls = some (lpsP.map Level.param) ∧ dCtors st cs = some csP) →
      (Frontend.denoteNList st'.ns names = some namesP ∧
        denoteLs st'.lss lvls = some (lpsP.map Level.param) ∧ dCtors st' cs = some csP) :=
    fun hx h => ⟨denoteNListE_ext hx _ _ h.1, denoteLs_ext h.2.1 hx,
      dCtors_ext hx _ _ h.2.2⟩
  split at hrun
  · rename_i hk
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    rw [if_pos hk]
    exact mapM_option_cons hp.2.2 rfl
  · rename_i hk
    rw [if_neg hk]
    obtain ⟨p1, hrel⟩ := mapM_pstep _ (fun m => csP.filter fun c =>
        ConLeche.ctorMember? namesP lpsP nP c == some m)
      (fun st b c => dCtors st b = some c)
      (fun _ st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss lvls = some (lpsP.map Level.param) ∧ dCtors st cs = some csP)
      (fun hx h => dCtors_ext hx _ _ h) (fun hx h => hPx hx h)
      (by
        intro m s₁ s₂ b hok1 hp1 hrun1
        exact filterM_pstep dCtor dCtor_ext
          (fun st => Frontend.denoteNList st.ns names = some namesP ∧
            denoteLs st.lss lvls = some (lpsP.map Level.param)) 
          (fun hx h => ⟨denoteNListE_ext hx _ _ h.1, denoteLs_ext h.2 hx⟩) _ _
          (by
            intro c cP t₀ t' bb hokt hpt hct hrunt
            obtain ⟨o, t₁, g1, g2⟩ := bindOk hrunt
            obtain ⟨q1, ho⟩ := ctorMember?_spec names namesP lvls lpsP nP c cP t₀ t₁ o hokt
              ⟨hpt.1, hpt.2, hct⟩ g1
            simp only [RV] at ho
            subst ho
            cases hcm : ConLeche.ctorMember? namesP lpsP nP cP with
            | none =>
              rw [hcm] at g2
              obtain ⟨rfl, rfl⟩ := pureOk g2
              exact ⟨q1, rfl⟩
            | some t =>
              rw [hcm] at g2
              obtain ⟨rfl, rfl⟩ := pureOk g2
              exact ⟨q1, by simp⟩)
          cs csP s₁ s₂ b hok1 ⟨hp1.1, hp1.2.1⟩ hp1.2.2 hrun1)
      (List.range k) s₀ s' r hok (fun _ _ => hp) hrun
    exact ⟨p1, ListRel.toMapM hrel⟩

/-! ## The recursor records' pins -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:325-333 blockRecLpsOk
Pure on both sides: `beq_nhandleList_eq` at every recursor, against the
block's level parameters (with the eliminator consed in front at the large
eliminator). -/
theorem blockRecLpsOk_spec {st : EStore} (hwf : StoreWF st) {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    Arena.blockRecLpsOk p = ConLeche.blockRecLpsOk pP := by
  have hlps := BlockShape.lps_spec h
  obtain ⟨ms, rs, el, s, hms, hrs, hel, -, hpP⟩ := dShape_inv h
  have hr : pP.recs = rs := by rw [hpP]
  have hl : pP.large = p.large := by rw [hpP]
  have he : pP.elim = el := by rw [hpP]
  have hcons : Frontend.denoteNList st.ns (p.elim :: p.lps) = some (el :: pP.lps) := by
    simp only [Frontend.denoteNList, hel, hlps]
  simp only [Arena.blockRecLpsOk, ConLeche.blockRecLpsOk, hr, hl, he]
  generalize pP.lps = L at hlps hcons
  clear h hms hpP hr
  generalize p.recs = xs at hrs
  induction xs generalizing rs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
    subst hrs; rfl
  | cons x xs ih =>
    obtain ⟨y, ys, rfl, hx, hxs⟩ := mapM_option_cons_inv hrs
    obtain ⟨cv, rhss, hcv, -, rfl⟩ := dRec_inv hx
    simp only [List.all_cons, ih ys hxs]
    congr 1
    cases p.large
    · exact beq_nhandleList_eq hwf (denoteCV_lps hcv) hlps
    · exact beq_nhandleList_eq hwf (denoteCV_lps hcv) hcons

/-- con-leche: none — `T_m.rec` at every member, interned in block order. -/
theorem recNames_run : ∀ (ms : List Arena.MemberShape) (msP : List ConLeche.MemberShape)
    (s₀ s' : AState) (want : List NIdx), StateOK s₀ →
    ms.mapM (dMember s₀.store) = some msP →
    ms.mapM (fun m => internNNode (.str m.cvT.name "rec")) s₀ = .ok (want, s') →
    PStep s₀ s' ∧
      Frontend.denoteNList s'.store.ns want = some (msP.map fun m => m.cvT.name.str "rec") := by
  intro ms
  induction ms with
  | nil =>
    intro msP s₀ s' want hok hms hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons m ms ih =>
    intro msP s₀ s' want hok hms hrun
    obtain ⟨mP, msP', rfl, hm, hxs⟩ := mapM_option_cons_inv hms
    obtain ⟨cv, cs, hcv, -, rfl⟩ := dMember_inv hm
    simp only [List.mapM_cons] at hrun
    obtain ⟨n, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, hn⟩ := internStrN_run hok (denoteCV_name hcv) h1
    obtain ⟨ns, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨p2, hns⟩ := ih msP' s₁ s₂ ns p1.ok
      (mapM_option_ext (fun x y h => dMember_ext p1.ext x y h) _ _ hxs) h3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨p1.trans p2, ?_⟩
    simp only [List.map_cons, Frontend.denoteNList, denoteN_ext hn p2.ext, hns]

/-- con-leche: none — the recursors' names, over the recursor list. -/
theorem recShapeNames_go {st : EStore} :
    ∀ {rs : List Arena.RecShape} {rsP : List ConLeche.RecShape},
      rs.mapM (dRec st) = some rsP →
      Frontend.denoteNList st.ns (rs.map (·.cvR.name)) = some (rsP.map (·.cvR.name)) := by
  intro rs
  induction rs with
  | nil =>
    intro rsP h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons r rs ih =>
    intro rsP h
    obtain ⟨rP, rsP', rfl, hr, hrs⟩ := mapM_option_cons_inv h
    obtain ⟨cv, rhss, hcv, -, rfl⟩ := dRec_inv hr
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hcv, ih hrs]

/-- con-leche: none — `all`/`contains` over two denoting name-handle lists is
the names'. -/
theorem all_contains_eq {st : EStore} (hwf : StoreWF st) {bs : List NIdx}
    {bsP : List ConLeche.Name} (hb : Frontend.denoteNList st.ns bs = some bsP) :
    ∀ {as : List NIdx} {asP : List ConLeche.Name},
      Frontend.denoteNList st.ns as = some asP →
      (as.all fun n => bs.contains n) = (asP.all fun n => bsP.contains n) := by
  intro as
  induction as with
  | nil =>
    intro asP h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro asP h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.all_cons, PW.contains_handle_eq hwf ha hb, ih has]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:335-357 blockRecNameSetOk
The recursor names as a SET.  The twin takes the members and the recursors
apart (the caller's `{ p with recs := own }` is an argument): stated at any
pure record `pP` whose two lists they denote. -/
theorem blockRecNameSetOk_spec (members : List Arena.MemberShape) (recs : List Arena.RecShape)
    (pP : ConLeche.BlockShape) :
    PSpec (fun st => members.mapM (dMember st) = some pP.members ∧
        recs.mapM (dRec st) = some pP.recs)
      (Arena.blockRecNameSetOk members recs) (RV (ConLeche.blockRecNameSetOk pP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hms, hrs⟩ := hp
  simp only [Arena.blockRecNameSetOk] at hrun
  obtain ⟨want, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hw⟩ := recNames_run members pP.members s₀ s₁ want hok hms h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  refine ⟨p1, ?_⟩
  have hg := recShapeNames_go (mapM_option_ext (fun x y h => dRec_ext p1.ext x y h) _ _ hrs)
  simp only [RV, ConLeche.blockRecNameSetOk]
  rw [PW.denoteNList_length hg, PW.denoteNList_length hw, all_contains_eq p1.ok.wf hg hw,
    all_contains_eq p1.ok.wf hw hg]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:449-454 litGuardNames — the ten
literal-guard names, off the pin table. -/
theorem litGuardNames_runB {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : Arena.litGuardNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.litGuardNames := by
  simp only [Arena.litGuardNames] at hr
  obtain ⟨n1, t1, g1, r1⟩ := bindOk hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.natName) hp rfl g1
  rw [e1] at r1
  obtain ⟨n2, t2, g2, r2⟩ := bindOk r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.natZeroName) hp rfl g2
  rw [e2] at r2
  obtain ⟨n3, t3, g3, r3⟩ := bindOk r2
  obtain ⟨e3, d3⟩ := pinAt_run (x := ConLeche.natSuccName) hp rfl g3
  rw [e3] at r3
  obtain ⟨n4, t4, g4, r4⟩ := bindOk r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.stringName) hp rfl g4
  rw [e4] at r4
  obtain ⟨n5, t5, g5, r5⟩ := bindOk r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.stringOfListName) hp rfl g5
  rw [e5] at r5
  obtain ⟨n6, t6, g6, r6⟩ := bindOk r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.listName) hp rfl g6
  rw [e6] at r6
  obtain ⟨n7, t7, g7, r7⟩ := bindOk r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.listNilName) hp rfl g7
  rw [e7] at r7
  obtain ⟨n8, t8, g8, r8⟩ := bindOk r7
  obtain ⟨e8, d8⟩ := pinAt_run (x := ConLeche.listConsName) hp rfl g8
  rw [e8] at r8
  obtain ⟨n9, t9, g9, r9⟩ := bindOk r8
  obtain ⟨e9, d9⟩ := pinAt_run (x := ConLeche.charName) hp rfl g9
  rw [e9] at r9
  obtain ⟨n10, t10, g10, r10⟩ := bindOk r9
  obtain ⟨e10, d10⟩ := pinAt_run (x := ConLeche.charOfNatName) hp rfl g10
  rw [e10] at r10
  obtain ⟨rfl, rfl⟩ := pureOk r10
  exact ⟨rfl, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, trivial⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:475-481 natOpNames —
`Bridge/Checker/DeclVal.lean`'s `natOpNames_run`, restated (that module is
not in this one's import closure). -/
theorem natOpNames_runB {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : Arena.natOpNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natOpNames := by
  simp only [Arena.natOpNames] at hr
  obtain ⟨n1, t1, g1, r1⟩ := bindOk hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.natPredName) hp rfl g1
  rw [e1] at r1
  obtain ⟨n2, t2, g2, r2⟩ := bindOk r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.natAddName) hp rfl g2
  rw [e2] at r2
  obtain ⟨n3, t3, g3, r3⟩ := bindOk r2
  obtain ⟨e3, d3⟩ := pinAt_run (x := ConLeche.natSubName) hp rfl g3
  rw [e3] at r3
  obtain ⟨n4, t4, g4, r4⟩ := bindOk r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.natMulName) hp rfl g4
  rw [e4] at r4
  obtain ⟨n5, t5, g5, r5⟩ := bindOk r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.natPowName) hp rfl g5
  rw [e5] at r5
  obtain ⟨n6, t6, g6, r6⟩ := bindOk r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.natBeqName) hp rfl g6
  rw [e6] at r6
  obtain ⟨n7, t7, g7, r7⟩ := bindOk r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.natBleName) hp rfl g7
  rw [e7] at r7
  obtain ⟨rfl, rfl⟩ := pureOk r7
  exact ⟨rfl, d1, d2, d3, d4, d5, d6, d7, trivial⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:483-498 natDivModNames —
`Bridge/Checker/DeclVal.lean`'s `natDivModNames_run`, restated. -/
theorem natDivModNames_runB {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : Arena.natDivModNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natDivModNames := by
  simp only [Arena.natDivModNames] at hr
  obtain ⟨n1, t1, g1, r1⟩ := bindOk hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.natDivName) hp rfl g1
  rw [e1] at r1
  obtain ⟨n2, t2, g2, r2⟩ := bindOk r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.natModName) hp rfl g2
  rw [e2] at r2
  obtain ⟨n3, t3, g3, r3⟩ := bindOk r2
  obtain ⟨e3, d3⟩ := pinAt_run (x := ConLeche.natGcdName) hp rfl g3
  rw [e3] at r3
  obtain ⟨n4, t4, g4, r4⟩ := bindOk r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.natLandName) hp rfl g4
  rw [e4] at r4
  obtain ⟨n5, t5, g5, r5⟩ := bindOk r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.natLorName) hp rfl g5
  rw [e5] at r5
  obtain ⟨n6, t6, g6, r6⟩ := bindOk r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.natXorName) hp rfl g6
  rw [e6] at r6
  obtain ⟨n7, t7, g7, r7⟩ := bindOk r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp rfl g7
  rw [e7] at r7
  obtain ⟨n8, t8, g8, r8⟩ := bindOk r7
  obtain ⟨e8, d8⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp rfl g8
  rw [e8] at r8
  obtain ⟨rfl, rfl⟩ := pureOk r8
  exact ⟨rfl, d1, d2, d3, d4, d5, d6, d7, d8, trivial⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:456-466 reservedRecName — the
`||` chain, one pin-table list at a time. -/
theorem reservedRecName_run {s s' : AState} {n : NIdx} {nm : ConLeche.Name} {b : Bool}
    (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hr : Arena.reservedRecName n s = .ok (b, s')) :
    PStep s s' ∧ b = ConLeche.reservedRecName nm := by
  simp only [Arena.reservedRecName] at hr
  obtain ⟨rs, s₁, h1, h2⟩ := bindOk hr
  obtain ⟨p1, hrs⟩ := reservedBasisNames_pstep hok hp h1
  have hn1 := denoteN_ext hn p1.ext
  have e1 := denoteNList_contains p1.ok.wf _ _ hrs _ _ hn1
  simp only [ConLeche.reservedRecName]
  rw [e1] at h2
  split at h2
  · rename_i hc
    obtain ⟨rfl, rfl⟩ := pureOk h2
    exact ⟨p1, by simp only [hc, Bool.true_or]⟩
  · rename_i hc
    simp only [Bool.not_eq_true] at hc
    have hp1 := hp.mono p1.ext p1.pins
    obtain ⟨ls, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨rfl, hls⟩ := litGuardNames_runB hp1 h3
    rw [denoteNList_contains p1.ok.wf _ _ (denoteNL_toList _ _ hls) _ _ hn1] at h4
    split at h4
    · rename_i hc2
      obtain ⟨rfl, rfl⟩ := pureOk h4
      exact ⟨p1, by simp only [hc, hc2, Bool.true_or, Bool.false_or]⟩
    · rename_i hc2
      simp only [Bool.not_eq_true] at hc2
      obtain ⟨os, s₃, h5, h6⟩ := bindOk h4
      obtain ⟨rfl, hos⟩ := natOpNames_runB hp1 h5
      rw [denoteNList_contains p1.ok.wf _ _ (denoteNL_toList _ _ hos) _ _ hn1] at h6
      split at h6
      · rename_i hc3
        obtain ⟨rfl, rfl⟩ := pureOk h6
        exact ⟨p1, by simp only [hc, hc2, hc3, Bool.true_or, Bool.false_or]⟩
      · rename_i hc3
        simp only [Bool.not_eq_true] at hc3
        obtain ⟨ds, s₄, h7, h8⟩ := bindOk h6
        obtain ⟨rfl, hds⟩ := natDivModNames_runB hp1 h7
        obtain ⟨rfl, rfl⟩ := pureOk h8
        refine ⟨p1, ?_⟩
        rw [denoteNList_contains p1.ok.wf _ _ (denoteNL_toList _ _ hds) _ _ hn1]
        simp only [hc, hc2, hc3, Bool.false_or]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:359-368 blockRecNamesUnreserved
No recursor takes a reserved name: the twin stops at the first hit, the pure
side is an `all`; `reservedRecName_run` at each.  **`PSpecP`**: the lists are
read off the pin table. -/
theorem blockRecNamesUnreserved_spec (pP : ConLeche.BlockShape) :
    ∀ (recs : List Arena.RecShape),
    PSpecP (fun st => recs.mapM (dRec st) = some pP.recs)
      (Arena.blockRecNamesUnreserved recs) (RV (ConLeche.blockRecNamesUnreserved pP)) := by
  intro recs
  simp only [ConLeche.blockRecNamesUnreserved]
  generalize pP.recs = rsP
  induction recs generalizing rsP with
  | nil =>
    intro s₀ s' r hok _ hrs hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
    subst hrs
    simp only [Arena.blockRecNamesUnreserved] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons rc rest ih =>
    intro s₀ s' r hok hp hrs hrun
    obtain ⟨rP, rsP', rfl, hr, hrest⟩ := mapM_option_cons_inv hrs
    obtain ⟨cv, rhss, hcv, -, rfl⟩ := dRec_inv hr
    simp only [Arena.blockRecNamesUnreserved] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, rfl⟩ := reservedRecName_run hok hp (denoteCV_name hcv) h1
    simp only [List.all_cons]
    split at h2
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨p1, by simp [hc]⟩
    · rename_i hc
      obtain ⟨p2, h3⟩ := ih rsP' s₁ s' r p1.ok (hp.mono p1.ext p1.pins)
        (mapM_option_ext (fun x y h => dRec_ext p1.ext x y h) _ _ hrest) h2
      refine ⟨p1.trans p2, ?_⟩
      simp only [RV] at h3 ⊢
      simp [hc, h3]

end ConRon.Bridge.Inductives
