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

/-! ## The record's projections -/

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
    obtain ⟨-, -, hcs⟩ := dMember_inv hm
    simp only [Arena.numCtorsOf, ConLeche.numCtorsOf, ih hms,
      ConLeche.option_mapM_length (f := dCtor st) hcs]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:131-132 BlockShape.k -/
theorem BlockShape.k_spec {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) : p.k = pP.k := by
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv h
  simp only [Arena.BlockShape.k, ConLeche.BlockShape.k, ConLeche.option_mapM_length hms]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:133-134 BlockShape.numCtors -/
theorem BlockShape.numCtors_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    p.numCtors = pP.numCtors := by
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv h
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
    obtain ⟨hcv, -, -⟩ := dMember_inv hm
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hcv, ih hms]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:137-138 BlockShape.memberNames
— the twin's name-handle list denotes con-leche's names. -/
theorem BlockShape.memberNames_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    Frontend.denoteNList st.ns p.memberNames = some pP.memberNames := by
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv h
  exact memberNames_go hms

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:139-140 BlockShape.nIdxs -/
theorem BlockShape.nIdxs_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) : p.nIdxs = pP.nIdxs := by
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv h
  simp only [Arena.BlockShape.nIdxs, ConLeche.BlockShape.nIdxs]
  clear h
  generalize pP.members = ms at hms ⊢
  generalize p.members = xs at hms
  induction xs generalizing ms with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms; rfl
  | cons m xs ih =>
    obtain ⟨mP, msP', rfl, hm, hxs⟩ := mapM_option_cons_inv hms
    simp only [List.map_cons, ih msP' hxs, (dMember_inv hm).2.1]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:141-144 BlockShape.lps -/
theorem BlockShape.lps_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    Frontend.denoteNList st.ns p.lps = some pP.lps := by
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv h
  simp only [Arena.BlockShape.lps, ConLeche.BlockShape.lps]
  generalize pP.members = ms at hms ⊢
  cases hm : p.members with
  | nil =>
    rw [hm] at hms
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms; rfl
  | cons m xs =>
    rw [hm] at hms
    obtain ⟨mP, msP', rfl, hm, -⟩ := mapM_option_cons_inv hms
    obtain ⟨hcv, -, -⟩ := dMember_inv hm
    simpa using denoteCV_lps hcv

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:145-147 BlockShape.allCtors -/
theorem BlockShape.allCtors_spec {st : EStore} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} (h : dShape st p = some pP) :
    dCtors st p.allCtors = some pP.allCtors := by
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv h
  simp only [Arena.BlockShape.allCtors, ConLeche.BlockShape.allCtors]
  clear h
  generalize pP.members = ms at hms ⊢
  generalize p.members = xs at hms
  induction xs generalizing ms with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms; rfl
  | cons m xs ih =>
    obtain ⟨mP, msP', rfl, hm, hxs⟩ := mapM_option_cons_inv hms
    obtain ⟨-, -, hcs⟩ := dMember_inv hm
    have h2 := ih msP' hxs
    simp only [dCtors] at h2 hcs ⊢
    simp only [List.map_cons, List.flatten_cons, List.mapM_append, hcs, h2,
      Option.bind_eq_bind, Option.pure_def, Option.bind_some]

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
  obtain ⟨hms, hrs, hnP, hel, -, hlg, -⟩ := dShape_inv (dShape_ext q.ext _ _ hp)
  simp only [dShape, hms, hrs, hnP, hel, hlg, denoteL_ext hs q.ext, ha,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp only [ConLeche.BlockShape.withSort]
  generalize Level.isEquiv sP Level.zero = v
  rcases v with _ | _ | _ <;> rfl

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
  have hlen := denoteNList_length hN
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
    obtain ⟨xs, x, hsp, -, hx⟩ := denoteBP_some hbp
    dsimp only at h2
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [if_pos htg] at h2
      obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨rfl, ho⟩ := viewBind_run h3
      cases o with
      | none => exact absurd h4 (fun hc => failDanglingE_ok hc)
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
          obtain ⟨rfl, ho2⟩ := viewConst_run h7
          cases o with
          | none => exact absurd h8 (fun hc => failDanglingE_ok hc)
          | some p =>
            obtain ⟨n, us⟩ := p
            have hw2 := view_of_viewConst_tag htc ho2.symm
            obtain ⟨nm, ls, hc, hn, -⟩ := denote_const_inv hok.wf hw2 hhd
            dsimp only at h8
            have hf := findIdx_handle_eq hok.wf hn hN
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
          | const c us => exact absurd (tag_const_of_denote hok.wf hhd) (by simpa using htc)
          | _ => rfl
    · rw [if_neg htg] at h2
      obtain ⟨rfl, rfl⟩ := pureOk h2
      refine ⟨PStep.refl hok, ?_⟩
      show names.length = _
      simp only [ConLeche.recTargetOf, hsp]
      rw [hlen]
      cases x with
      | forallE d b m => exact absurd (tag_forallE_of_denote hok.wf hx) (by simpa using htg)
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
    obtain ⟨xs, x, hsp, -, hx⟩ := denoteBP_some hbp
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
  obtain ⟨-, hrs, -, hel, -, hl, -⟩ := dShape_inv h
  have hcons : Frontend.denoteNList st.ns (p.elim :: p.lps) = some (pP.elim :: pP.lps) := by
    simp only [Frontend.denoteNList, hel, hlps]
  simp only [Arena.blockRecLpsOk, ConLeche.blockRecLpsOk, ← hl]
  generalize pP.lps = L at hlps hcons
  generalize pP.recs = rs at hrs ⊢
  clear h
  generalize p.recs = xs at hrs
  induction xs generalizing rs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
    subst hrs; rfl
  | cons x xs ih =>
    obtain ⟨y, ys, rfl, hx, hxs⟩ := mapM_option_cons_inv hrs
    obtain ⟨hcv, -, -, -, -⟩ := dRec_inv hx
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
    obtain ⟨hcv, -, -⟩ := dMember_inv hm
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
    obtain ⟨hcv, -, -, -, -⟩ := dRec_inv hr
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
        simp only [List.all_cons, contains_handle_eq hwf ha hb, ih has]

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
  rw [denoteNList_length hg, denoteNList_length hw, all_contains_eq p1.ok.wf hg hw,
    all_contains_eq p1.ok.wf hw hg]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:449-454 litGuardNames — the ten
literal-guard names, off the pin table. -/
theorem litGuardNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
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
    obtain ⟨rfl, hls⟩ := litGuardNames_run hp1 h3
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
    obtain ⟨hcv, -, -, -, -⟩ := dRec_inv hr
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

/-! ## The members' counts -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:370-383 blockMemberCounts?
(`rec_for_member`) — the twin's `findM?` over the recursors is con-leche's
`find?`, read at the two counts the member's reader takes. -/
theorem recForMember_run (names : List NIdx) (namesP : List ConLeche.Name) (m : Nat) :
    ∀ (rs : List (IConstantVal × Nat × Nat × List IRecRule))
      (rsP : List (ConstantVal × Nat × Nat × List RecRule)) (s₀ s' : AState)
      (o : Option (IConstantVal × Nat × Nat × List IRecRule)), StateOK s₀ →
      Frontend.denoteNList s₀.store.ns names = some namesP →
      rs.mapM (dRec4 s₀.store) = some rsP →
      (rs.findM? (fun q => (do pure ((← Arena.recTargetOf names q.2.1 q.1.type) == m) :
        AM Bool)) : AM _) s₀ = .ok (o, s') →
      PStep s₀ s' ∧ o.map (fun q => (q.2.1, q.2.2.1)) =
        (rsP.find? fun q => ConLeche.recTargetOf namesP q.2.1 q.1.type == m).map
          (fun q => (q.2.1, q.2.2.1)) := by
  intro rs
  induction rs with
  | nil =>
    intro rsP s₀ s' o hok _ hrs hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
    subst hrs
    simp only [List.findM?] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons q qs ih =>
    intro rsP s₀ s' o hok hN hrs hrun
    obtain ⟨qP, qsP, rfl, hq, hqs⟩ := mapM_option_cons_inv hrs
    obtain ⟨hcv, hmI, hrP, -⟩ := dRec4_inv hq
    simp only [List.findM?] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨t, s₂, h3, h4⟩ := bindOk h1
    obtain ⟨p3, ht⟩ := recTargetOf_spec names namesP q.2.1 q.1.type qP.1.type s₀ s₂ t hok
      ⟨hN, denoteCV_type hcv⟩ h3
    simp only [RV] at ht
    subst ht
    obtain ⟨rfl, rfl⟩ := pureOk h4
    simp only [List.find?_cons]
    cases hb : (ConLeche.recTargetOf namesP qP.2.1 qP.1.type == m) with
    | true =>
      rw [hmI, hb] at h2
      obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨p3, by simp [hmI, hrP]⟩
    | false =>
      rw [hmI, hb] at h2
      obtain ⟨p4, h5⟩ := ih qsP _ s' o p3.ok (denoteNListE_ext p3.ext _ _ hN)
        (mapM_option_ext (fun x y h => dRec4_ext p3.ext x y h) _ _ hqs) h2
      exact ⟨p3.trans p4, h5⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:370-383 blockMemberCounts?
The members' index counts, member by member: `recForMember_run`, then
`blockCounts?_spec`. -/
theorem blockMemberCounts?_spec (nPd k nC : Nat) (names : List NIdx)
    (namesP : List ConLeche.Name) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (rsP : List (ConstantVal × Nat × Nat × List RecRule)) :
    ∀ (m : Nat) (cvTs : List IConstantVal) (cvTsP : List ConstantVal),
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        rs.mapM (dRec4 st) = some rsP ∧ cvTs.mapM (Frontend.denoteCV st) = some cvTsP)
      (Arena.blockMemberCounts? nPd k nC names rs m cvTs)
      (RV (ConLeche.blockMemberCounts? nPd k nC namesP rsP m cvTsP)) := by
  intro m cvTs
  induction cvTs generalizing m with
  | nil =>
    intro cvTsP s₀ s' r hok hp hrun
    obtain ⟨-, -, hc⟩ := hp
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hc
    subst hc
    simp only [Arena.blockMemberCounts?] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons cvT ts ih =>
    intro cvTsP s₀ s' r hok hp hrun
    obtain ⟨hN, hrs, hc⟩ := hp
    obtain ⟨cvTP, tsP, rfl, hcv, hts⟩ := mapM_option_cons_inv hc
    have hlen : rs.length = rsP.length := (ConLeche.option_mapM_length hrs).symm
    simp only [Arena.blockMemberCounts?] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := recForMember_run names namesP m rs rsP s₀ s₁ o hok hN hrs h1
    obtain ⟨c, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨rr, hrr, h3⟩ : ∃ rr, rr = (rsP.find? fun q =>
          ConLeche.recTargetOf namesP q.2.1 q.1.type == m).map (fun q => (q.2.1, q.2.2.1)) ∧
        Arena.blockCounts? nPd k nC rs.length cvT rr s₁ = .ok (c, s₂) := by
      cases o with
      | none => exact ⟨none, by rw [← ho]; rfl, h3⟩
      | some q => exact ⟨_, by rw [← ho]; rfl, h3⟩
    subst hrr
    rw [hlen] at h3
    obtain ⟨p3, hc3⟩ := blockCounts?_spec nPd k nC rsP.length cvT cvTP _ s₁ s₂ c p1.ok
      (denoteCV_ext hcv p1.ext) h3
    simp only [RV] at hc3
    subst hc3
    simp only [ConLeche.blockMemberCounts?]
    cases hbc : ConLeche.blockCounts? nPd k nC rsP.length cvTP
        ((rsP.find? fun q => ConLeche.recTargetOf namesP q.2.1 q.1.type == m).map
          fun q => (q.2.1, q.2.2.1)) with
    | none =>
      rw [hbc] at h4
      obtain ⟨rfl, rfl⟩ := pureOk h4
      exact ⟨p1.trans p3, rfl⟩
    | some cc =>
      rw [hbc] at h4
      dsimp only at h4
      obtain ⟨ns, s₃, h5, h6⟩ := bindOk h4
      have x3 := p1.ext.trans p3.ext
      obtain ⟨p5, hns⟩ := ih (m + 1) tsP s₂ s₃ ns p3.ok
        ⟨denoteNListE_ext x3 _ _ hN,
         mapM_option_ext (fun x y h => dRec4_ext x3 x y h) _ _ hrs,
         mapM_option_ext (fun x y h => denoteCV_ext h x3) _ _ hts⟩ h5
      simp only [RV] at hns
      subst hns
      cases hrest : ConLeche.blockMemberCounts? nPd k nC namesP rsP (m + 1) tsP with
      | none =>
        rw [hrest] at h6
        obtain ⟨rfl, rfl⟩ := pureOk h6
        exact ⟨(p1.trans p3).trans p5, rfl⟩
      | some ns =>
        rw [hrest] at h6
        obtain ⟨rfl, rfl⟩ := pureOk h6
        exact ⟨(p1.trans p3).trans p5, rfl⟩

/-! ## The recogniser -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
(the result sort) — member 0's sort, or the placeholder `0`. -/
def resSortOfP (ty : Expr) (k : Nat) : Level :=
  match ty.stripPis k with
  | some (_, .sort s) => s
  | _ => .zero

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
(`large?`) — which eliminator the first recursor claims. -/
def largeOfP (lps : List ConLeche.Name) : List ConLeche.Name → Option ConLeche.Name
  | elim :: relps => if relps == lps && !lps.contains elim then some elim else none
  | [] => none

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
(after the pins) — the record, the pure side's stretch the twin duplicates
into its three result-sort arms. -/
def shapeTailP (nPd : Nat) (cvT0 cvR0 : ConstantVal) (cvTs : List ConstantVal)
    (cs : List (ConstantVal × Nat × Nat)) (rs : List (ConstantVal × Nat × Nat × List RecRule))
    (nIdxs : List Nat) : Option ConLeche.BlockShape :=
  let lps := cvT0.levelParams
  let names := cvTs.map (·.name)
  let k := cvTs.length
  let s := resSortOfP cvT0.type (nPd + nIdxs.headD 0)
  let isProp := Level.isEquiv s .zero == some true
  let ctors : List (ConstantVal × Nat) := cs.map fun c => (c.1, c.2.2)
  let groups := ConLeche.blockGroups names lps nPd k ctors
  let members := ((cvTs.zip nIdxs).zip groups).map
    fun (a : (ConstantVal × Nat) × List (ConstantVal × Nat)) =>
      (⟨a.1.1, a.1.2, a.2⟩ : ConLeche.MemberShape)
  let recsL := rs.map fun (r : ConstantVal × Nat × Nat × List RecRule) =>
    (⟨r.1, r.2.2.1, r.2.1, ConLeche.recTargetOf names r.2.1 r.1.type,
      r.2.2.2.map RecRule.rhs⟩ : ConLeche.RecShape)
  match largeOfP lps cvR0.levelParams with
  | some elim => some ⟨members, recsL, nPd, elim, s, true, isProp⟩
  | none => some ⟨members, recsL, nPd, .anonymous, s, false, isProp⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
(after the split) — the pure recogniser with its inline `match`es named. -/
def shapeOfSplitP (nPd : Nat) (cvTs : List ConstantVal) (cs : List (ConstantVal × Nat × Nat))
    (rs : List (ConstantVal × Nat × Nat × List RecRule)) : Option ConLeche.BlockShape :=
  match cvTs, rs with
  | cvT0 :: _, (cvR0, _, _, _) :: _ =>
    let lps := cvT0.levelParams
    let names := cvTs.map (·.name)
    let k := cvTs.length
    match ConLeche.blockMemberCounts? nPd k cs.length names rs 0 cvTs with
    | none => none
    | some nIdxs =>
      if (cvTs.all fun c => reservedBasisNames.contains c.name == false) &&
          (rs.all fun r => reservedBasisNames.contains r.1.name == false) &&
          (cvTs.all fun c => c.levelParams == lps) &&
          cs.all (fun c => c.2.1 == nPd && c.1.levelParams == lps &&
            reservedBasisNames.contains c.1.name == false) then
        shapeTailP nPd cvT0 cvR0 cvTs cs rs nIdxs
      else none
  | _, _ => none

theorem blockShape_eq (nPd : Nat) (block : List ConstantInfo) :
    ConLeche.blockShape? nPd block =
      (ConLeche.blockSplit block).bind fun q => shapeOfSplitP nPd q.1 q.2.1 q.2.2 := by
  unfold ConLeche.blockShape?
  rcases ConLeche.blockSplit block with _ | ⟨cvTs, cs, rs⟩
  · rfl
  · simp only [Option.bind_some, shapeOfSplitP]
    rcases cvTs with _ | ⟨cvT0, cvTs⟩ <;> rcases rs with _ | ⟨⟨cvR0, a, b, c⟩, rs⟩ <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
(after the result sort) — the twin's stretch its `do` block duplicates into
the three result-sort arms, written once. -/
def shapeTailM (nPd : Nat) (cvT0 cvR0 : IConstantVal) (cvTs : List IConstantVal)
    (cs : List (IConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (nIdxs : List Nat) (y : LIdx) : AM (Option Arena.BlockShape) := do
  let z ← zeroLevel
  let eq ← lvlEq? y z
  let lvls ← paramLevels cvT0.levelParams
  let groups ← Arena.blockGroups (cvTs.map (·.name)) lvls nPd cvTs.length
    (cs.map fun c => (c.1, c.2.2))
  let recsL ← rs.mapM fun r => do
    let tgt ← Arena.recTargetOf (cvTs.map (·.name)) r.2.1 r.1.type
    pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : Arena.RecShape)
  match (match cvR0.levelParams with
      | [] => none
      | elim :: relps =>
        if (relps == cvT0.levelParams && !cvT0.levelParams.contains elim) = true then some elim
        else none) with
  | some elim =>
    pure (some { members := ((cvTs.zip nIdxs).zip groups).map
                   (fun a => { cvT := a.1.1, nIdx := a.1.2, ctors := a.2 }),
                 recs := recsL, nP := nPd, elim := elim, resSort := y, large := true,
                 isProp := match eq with
                   | some true => true
                   | some false => false
                   | none => false })
  | none => do
    let anon ← internNNode NNodeView.anonymous
    pure (some { members := ((cvTs.zip nIdxs).zip groups).map
                   (fun a => { cvT := a.1.1, nIdx := a.1.2, ctors := a.2 }),
                 recs := recsL, nP := nPd, elim := anon, resSort := y, large := false,
                 isProp := match eq with
                   | some true => true
                   | some false => false
                   | none => false })

/-- con-leche: none — the formers' names, over the former list. -/
theorem cvNames_go {st : EStore} :
    ∀ {cvs : List IConstantVal} {cvsP : List ConstantVal},
      cvs.mapM (Frontend.denoteCV st) = some cvsP →
      Frontend.denoteNList st.ns (cvs.map (·.name)) = some (cvsP.map (·.name)) := by
  intro cvs
  induction cvs with
  | nil =>
    intro cvsP h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons c cs ih =>
    intro cvsP h
    obtain ⟨cP, csP, rfl, hc, hcs⟩ := mapM_option_cons_inv h
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hc, ih hcs]

/-- con-leche: none — the recogniser's constructor list, read off the
split's. -/
theorem denoteCtors3_dCtors {st : EStore} :
    ∀ (cs : List (IConstantVal × Nat × Nat)) (csP : List (ConstantVal × Nat × Nat)),
      denoteCtors3 st cs = some csP →
      dCtors st (cs.map fun c => (c.1, c.2.2)) = some (csP.map fun c => (c.1, c.2.2)) := by
  intro cs
  induction cs with
  | nil => intro csP h; simp only [denoteCtors3, Option.some.injEq] at h; subst h; rfl
  | cons c cs ih =>
    intro csP h
    obtain ⟨cv, a, b⟩ := c
    simp only [denoteCtors3] at h
    cases h1 : Frontend.denoteCV st cv with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : denoteCtors3 st cs with
      | none => rw [h1, h2] at h; simp at h
      | some xs =>
        rw [h1, h2] at h
        obtain rfl := (Option.some.inj h).symm
        have := ih xs h2
        simp only [dCtors] at this ⊢
        simp only [List.map_cons]
        exact mapM_option_cons (by simp [dCtor, h1]) this

/-- con-leche: none — a three-tuple constructor list survives an append. -/
theorem denoteCtors3_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (cs : List (IConstantVal × Nat × Nat)) (csP : List (ConstantVal × Nat × Nat)),
      denoteCtors3 st cs = some csP → denoteCtors3 st' cs = some csP := by
  intro cs
  induction cs with
  | nil => intro csP h; exact h
  | cons c cs ih =>
    intro csP h
    obtain ⟨cv, a, b⟩ := c
    simp only [denoteCtors3] at h ⊢
    cases h1 : Frontend.denoteCV st cv with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : denoteCtors3 st cs with
      | none => rw [h1, h2] at h; simp at h
      | some xs =>
        rw [h1, h2] at h
        rw [denoteCV_ext h1 hx, ih xs h2]
        exact h

/-- con-leche: none — the rules' right-hand sides denote. -/
theorem denoteRules_rhss {st : EStore} :
    ∀ (rs : List IRecRule) (rsP : List RecRule),
      Frontend.denoteRules st rs = some rsP →
      Frontend.denoteEList st (rs.map (·.rhs)) = some (rsP.map (·.rhs)) := by
  intro rs
  induction rs with
  | nil => intro rsP h; simp only [Frontend.denoteRules, Option.some.injEq] at h; subst h; rfl
  | cons r rs ih =>
    intro rsP h
    simp only [Frontend.denoteRules] at h
    cases h1 : Frontend.denoteRule st r with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : Frontend.denoteRules st rs with
      | none => rw [h1, h2] at h; simp at h
      | some xs =>
        rw [h1, h2] at h
        obtain rfl := (Option.some.inj h).symm
        simp only [List.map_cons, Frontend.denoteEList, denoteRule_rhs h1, ih xs h2]

/-- con-leche: none — the recursor records, each with the member its MAJOR
names (`recTargetOf_spec` at each). -/
theorem recsL_run (names : List NIdx) (namesP : List ConLeche.Name) :
    ∀ (rs : List (IConstantVal × Nat × Nat × List IRecRule))
      (rsP : List (ConstantVal × Nat × Nat × List RecRule)) (s₀ s' : AState)
      (out : List Arena.RecShape), StateOK s₀ →
      Frontend.denoteNList s₀.store.ns names = some namesP →
      rs.mapM (dRec4 s₀.store) = some rsP →
      (rs.mapM fun r => (do
          let tgt ← Arena.recTargetOf names r.2.1 r.1.type
          pure (⟨r.1, r.2.2.1, r.2.1, tgt, r.2.2.2.map (·.rhs)⟩ : Arena.RecShape) :
            AM Arena.RecShape)) s₀ =
        .ok (out, s') →
      PStep s₀ s' ∧ out.mapM (dRec s'.store) = some (rsP.map fun r =>
        (⟨r.1, r.2.2.1, r.2.1, ConLeche.recTargetOf namesP r.2.1 r.1.type,
          r.2.2.2.map RecRule.rhs⟩ : ConLeche.RecShape)) := by
  intro rs
  induction rs with
  | nil =>
    intro rsP s₀ s' out hok _ hrs hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
    subst hrs
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons q qs ih =>
    intro rsP s₀ s' out hok hN hrs hrun
    obtain ⟨qP, qsP, rfl, hq, hqs⟩ := mapM_option_cons_inv hrs
    obtain ⟨hcv, hmI, hrP, hru⟩ := dRec4_inv hq
    simp only [List.mapM_cons] at hrun
    obtain ⟨x, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨t, s₂, h3, h4⟩ := bindOk h1
    obtain ⟨p3, ht⟩ := recTargetOf_spec names namesP q.2.1 q.1.type qP.1.type s₀ s₂ t hok
      ⟨hN, denoteCV_type hcv⟩ h3
    simp only [RV] at ht
    subst ht
    obtain ⟨rfl, rfl⟩ := pureOk h4
    obtain ⟨xs, s₃, h5, h6⟩ := bindOk h2
    obtain ⟨p5, h7⟩ := ih qsP _ s₃ xs p3.ok (denoteNListE_ext p3.ext _ _ hN)
      (mapM_option_ext (fun x y h => dRec4_ext p3.ext x y h) _ _ hqs) h5
    obtain ⟨rfl, rfl⟩ := pureOk h6
    refine ⟨p3.trans p5, ?_⟩
    have x5 := p3.ext.trans p5.ext
    simp only [List.map_cons]
    refine mapM_option_cons ?_ h7
    simp only [dRec, denoteCV_ext hcv x5, denoteRules_rhss _ _ (denoteRules_ext x5 _ _ hru),
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, hmI, hrP]

/-- con-leche: none — the members, zipped from the formers, their counts and
their groups. -/
theorem members_denote {st : EStore} :
    ∀ (cvTs : List IConstantVal) (cvTsP : List ConstantVal) (nIdxs : List Nat)
      (groups : List (List (IConstantVal × Nat))) (groupsP : List (List (ConstantVal × Nat))),
      cvTs.mapM (Frontend.denoteCV st) = some cvTsP → groups.mapM (dCtors st) = some groupsP →
      (((cvTs.zip nIdxs).zip groups).map
          (fun a => ({ cvT := a.1.1, nIdx := a.1.2, ctors := a.2 } : Arena.MemberShape))).mapM
        (dMember st) =
        some (((cvTsP.zip nIdxs).zip groupsP).map
          (fun a => (⟨a.1.1, a.1.2, a.2⟩ : ConLeche.MemberShape))) := by
  intro cvTs
  induction cvTs with
  | nil =>
    intro cvTsP nIdxs groups groupsP h1 _
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h1
    subst h1; rfl
  | cons c cs ih =>
    intro cvTsP nIdxs groups groupsP h1 h2
    obtain ⟨cP, csP, rfl, hc, hcs⟩ := mapM_option_cons_inv h1
    cases nIdxs with
    | nil => rfl
    | cons n ns =>
      cases groups with
      | nil =>
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h2
        subst h2; rfl
      | cons g gs =>
        obtain ⟨gP, gsP, rfl, hg, hgs⟩ := mapM_option_cons_inv h2
        simp only [List.zip_cons_cons, List.map_cons]
        refine mapM_option_cons ?_ (ih csP ns gs gsP hcs hgs)
        simp only [dMember, hc, hg, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
— **the record, once the result sort is read**: `lvlEq?` (CORE: the cache
licence), `paramLevels`, `blockGroups_spec`, `recsL_run`, the eliminator. -/
theorem shapeTail_run {μ : CheckMode} {env : Env} {fe : IFEnv} (nPd : Nat)
    (cvT0 cvR0 : IConstantVal) (cvT0P cvR0P : ConstantVal) (cvTs : List IConstantVal)
    (cvTsP : List ConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (csP : List (ConstantVal × Nat × Nat)) (rs : List (IConstantVal × Nat × Nat × List IRecRule))
    (rsP : List (ConstantVal × Nat × Nat × List RecRule)) (nIdxs : List Nat) (y : LIdx)
    {s₀ s s' : AState} {r : Option Arena.BlockShape}
    (hc : CheckOK μ env fe s₀) (q : PStep s₀ s)
    (hT0 : Frontend.denoteCV s.store cvT0 = some cvT0P)
    (hR0 : Frontend.denoteCV s.store cvR0 = some cvR0P)
    (hTs : cvTs.mapM (Frontend.denoteCV s.store) = some cvTsP)
    (hcs : denoteCtors3 s.store cs = some csP) (hrs : rs.mapM (dRec4 s.store) = some rsP)
    (hy : denoteL s.store.ls y = some (resSortOfP cvT0P.type (nPd + nIdxs.headD 0)))
    (hrun : shapeTailM nPd cvT0 cvR0 cvTs cs rs nIdxs y s = .ok (r, s')) :
    PStep s₀ s' ∧ ROp (fun q st p => dShape st p = some q)
      (shapeTailP nPd cvT0P cvR0P cvTsP csP rsP nIdxs) s'.store r := by
  simp only [shapeTailM] at hrun
  obtain ⟨z, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨e, s2, k2, z2⟩ := bindOk z1
  obtain ⟨-, he⟩ := lvlEqZero_run hc q hy k1 k2
  obtain ⟨hs1, -⟩ := zeroLevel_run (hc.pins.mono q.ext q.pins) k1
  subst hs1
  have p2 : PStep s1 s2 := lvlEq?_pstep q.ok k2
  obtain ⟨lvls, s3, k3, z3⟩ := bindOk z2
  have hlps := denoteCV_lps hT0
  obtain ⟨p3, hl⟩ := paramLevels_spec _ _ s2 s3 lvls p2.ok
    (denoteNListE_ext p2.ext _ _ hlps) k3
  have x3 := p2.ext.trans p3.ext
  obtain ⟨groups, s4, k4, z4⟩ := bindOk z3
  have hlenT : cvTs.length = cvTsP.length := (ConLeche.option_mapM_length hTs).symm
  rw [hlenT] at k4
  have g1 := denoteNListE_ext x3 _ _ (cvNames_go hTs)
  have g3 := dCtors_ext x3 _ _ (denoteCtors3_dCtors cs csP hcs)
  have G := blockGroups_spec (cvTs.map (·.name)) (cvTsP.map (·.name)) lvls
    cvT0P.levelParams nPd cvTsP.length (cs.map fun c => (c.1, c.2.2))
    (csP.map fun c => (c.1, c.2.2))
  have G2 := G s3 s4 groups p3.ok ⟨g1, hl, g3⟩
  have k4' : Arena.blockGroups (cvTs.map (·.name)) lvls nPd cvTsP.length
      (cs.map fun c => (c.1, c.2.2)) s3 = .ok (groups, s4) := k4
  have R := G2 k4'
  have p4 := R.1
  have hg : groups.mapM (dCtors s4.store) = some (ConLeche.blockGroups (cvTsP.map (·.name))
      cvT0P.levelParams nPd cvTsP.length (csP.map fun c => (c.1, c.2.2))) := R.2
  have x4 := x3.trans p4.ext
  obtain ⟨recsL, s5, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hR⟩ := recsL_run (cvTs.map (·.name)) (cvTsP.map (·.name)) rs rsP s4 s5 recsL
    p4.ok (denoteNListE_ext x4 _ _ (cvNames_go hTs))
    (mapM_option_ext (fun a b h => dRec4_ext x4 a b h) _ _ hrs) k5
  have x5 := x4.trans p5.ext
  have q5 : PStep s1 s5 := ((p2.trans p3).trans p4).trans p5
  have hmem := members_denote cvTs cvTsP nIdxs groups _
    (mapM_option_ext (fun a b h => denoteCV_ext h (x4.trans p5.ext)) _ _ hTs)
    (mapM_option_ext (fun a b h => dCtors_ext p5.ext a b h) _ _ hg)
  have hy5 : denoteL s5.store.ls y = some (resSortOfP cvT0P.type (nPd + nIdxs.headD 0)) :=
    denoteL_ext hy x5
  have hRlps := denoteCV_lps hR0
  simp only [shapeTailP]
  cases hlp : cvR0.levelParams with
  | nil =>
    have hlpP : cvR0P.levelParams = [] := by
      rw [hlp] at hRlps; simp [Frontend.denoteNList] at hRlps; exact hRlps
    rw [hlp] at z5
    simp only [hlpP, largeOfP]
    obtain ⟨anon, sA, kA, zA⟩ := bindOk z5
    obtain ⟨pA, hanon⟩ := internNNode_run p5.ok
      (by intro c hc; simp [NNodeView.children] at hc) kA
    obtain ⟨rfl, rfl⟩ := pureOk zA
    refine ⟨q.trans (q5.trans pA), _, rfl, ?_⟩
    simp only [dShape, mapM_option_ext (fun a b h => dMember_ext pA.ext a b h) _ _ hmem,
      mapM_option_ext (fun a b h => dRec_ext pA.ext a b h) _ _ hR, hanon, denoteNView,
      denoteL_ext hy5 pA.ext, he, isProp_match_eq, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  | cons elim relps =>
    rw [hlp] at hRlps
    simp only [Frontend.denoteNList] at hRlps
    cases helim : denoteN s1.store.ns elim with
    | none => rw [helim] at hRlps; simp at hRlps
    | some elimP =>
    cases hrel : Frontend.denoteNList s1.store.ns relps with
    | none => rw [helim, hrel] at hRlps; simp at hRlps
    | some relpsP =>
    rw [helim, hrel] at hRlps
    have hlpP : cvR0P.levelParams = elimP :: relpsP := (Option.some.inj hRlps).symm
    have xs5 : Ext s1.store s5.store := q5.ext
    have g8 : (relps == cvT0.levelParams) = (relpsP == cvT0P.levelParams) :=
      beq_nhandleList_eq p5.ok.wf (denoteNListE_ext xs5 _ _ hrel)
        (denoteNListE_ext xs5 _ _ hlps)
    have g9 : cvT0.levelParams.contains elim = cvT0P.levelParams.contains elimP :=
      denoteNList_contains p5.ok.wf _ _ (denoteNListE_ext xs5 _ _ hlps) _ _
        (denoteN_ext helim xs5)
    rw [hlp] at z5
    dsimp only at z5
    simp only [hlpP, largeOfP]
    rw [g8, g9] at z5
    by_cases hc2 : (relpsP == cvT0P.levelParams && !cvT0P.levelParams.contains elimP) = true
    · rw [if_pos hc2] at z5 ⊢
      obtain ⟨rfl, rfl⟩ := pureOk z5
      refine ⟨q.trans q5, _, rfl, ?_⟩
      simp only [dShape, hmem, hR, denoteN_ext helim xs5, hy5, he, isProp_match_eq,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · rw [if_neg hc2] at z5 ⊢
      obtain ⟨anon, sA, kA, zA⟩ := bindOk z5
      obtain ⟨pA, hanon⟩ := internNNode_run p5.ok
        (by intro c hc; simp [NNodeView.children] at hc) kA
      obtain ⟨rfl, rfl⟩ := pureOk zA
      refine ⟨q.trans (q5.trans pA), _, rfl, ?_⟩
      simp only [dShape, mapM_option_ext (fun a b h => dMember_ext pA.ext a b h) _ _ hmem,
        mapM_option_ext (fun a b h => dRec_ext pA.ext a b h) _ _ hR, hanon, denoteNView,
        denoteL_ext hy5 pA.ext, he, isProp_match_eq, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]

/-- con-leche: none — an `all` over a `mapM`-denoting list is the pure
`all` when the two tests agree pointwise. -/
theorem all_mapM_eq {α β : Type} {d : α → Option β} {f : α → Bool} {g : β → Bool}
    (h : ∀ x y, d x = some y → f x = g y) :
    ∀ (xs : List α) (ys : List β), xs.mapM d = some ys → xs.all f = ys.all g := by
  intro xs
  induction xs with
  | nil =>
    intro ys hm
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
    subst hm; rfl
  | cons x xs ih =>
    intro ys hm
    obtain ⟨y, ys', rfl, hx, hxs⟩ := mapM_option_cons_inv hm
    simp only [List.all_cons, h x y hx, ih ys' hxs]

/-- con-leche: none — the same over a three-tuple constructor list. -/
theorem all_ctors3_eq {st : EStore} {f : IConstantVal × Nat × Nat → Bool}
    {g : ConstantVal × Nat × Nat → Bool}
    (h : ∀ cv a b cvP, Frontend.denoteCV st cv = some cvP → f (cv, a, b) = g (cvP, a, b)) :
    ∀ (cs : List (IConstantVal × Nat × Nat)) (csP : List (ConstantVal × Nat × Nat)),
      denoteCtors3 st cs = some csP → cs.all f = csP.all g := by
  intro cs
  induction cs with
  | nil => intro csP hc; simp only [denoteCtors3, Option.some.injEq] at hc; subst hc; rfl
  | cons c cs ih =>
    intro csP hc
    obtain ⟨cv, a, b⟩ := c
    simp only [denoteCtors3] at hc
    cases h1 : Frontend.denoteCV st cv with
    | none => rw [h1] at hc; simp at hc
    | some x =>
      cases h2 : denoteCtors3 st cs with
      | none => rw [h1, h2] at hc; simp at hc
      | some xs =>
        rw [h1, h2] at hc
        obtain rfl := (Option.some.inj hc).symm
        simp only [List.all_cons, h cv a b x h1, ih xs h2]

/-- con-leche: none — an `all` of a conjunction splits. -/
theorem all_and_split {α : Type} (p q : α → Bool) :
    ∀ (xs : List α), (xs.all fun a => p a && q a) = (xs.all p && xs.all q) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, ih]
    cases p x <;> cases q x <;> cases xs.all p <;> cases xs.all q <;> rfl

theorem not_eq_beq_false {a b : Bool} (h : a = b) : (!a) = (b == false) := by
  subst h; cases a <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
— **the recogniser's run, inverted once**: the split (`blockSplit_spec`), the
counts, the pins (reassociated: the twin reads the formers' two pins in one
pass), the result sort's three arms, each into `shapeTail_run`. -/
theorem blockShape?_run {μ : CheckMode} {env : Env} {fe : IFEnv} (nPd : Nat)
    (block : List IConstantInfo) (blockP : List ConstantInfo) (s₀ s' : AState)
    (r : Option Arena.BlockShape) (hc : CheckOK μ env fe s₀)
    (hb : Frontend.denoteCIList s₀.store block = some blockP)
    (hrun : Arena.blockShape? nPd block s₀ = .ok (r, s')) :
    PStep s₀ s' ∧
      ROp (fun q st p => dShape st p = some q) (ConLeche.blockShape? nPd blockP) s'.store r := by
  have hok := hc.state
  rw [blockShape_eq]
  have hsp := blockSplit_spec s₀.store block blockP hb
  unfold Arena.blockShape? at hrun
  cases hA : Arena.blockSplit block with
  | none =>
    rw [hA] at hrun hsp
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    simp only [ROp] at hsp ⊢
    rw [hsp]; rfl
  | some a =>
    rw [hA] at hrun hsp
    obtain ⟨q, hq, hrel⟩ := hsp
    rw [hq, Option.bind_some]
    obtain ⟨cvTs, cs, rs⟩ := a
    obtain ⟨cvTsP, csP, rsP⟩ := q
    obtain ⟨hTs, hcs, hrs⟩ := hrel
    dsimp only at hTs hcs hrs hrun ⊢
    rcases cvTs with _ | ⟨cvT0, cvTs'⟩
    · simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hTs
      subst hTs
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨PStep.refl hok, rfl⟩
    rcases rs with _ | ⟨⟨cvR0, mI0, rP0, rules0⟩, rs'⟩
    · simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrs
      subst hrs
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show _ = none
      rcases cvTsP <;> rfl
    obtain ⟨cvT0P, cvTsP', rfl, hT0, -⟩ := mapM_option_cons_inv hTs
    obtain ⟨r0P, rsP', rfl, hr0, -⟩ := mapM_option_cons_inv hrs
    obtain ⟨hR0, -, -, -⟩ := dRec4_inv hr0
    obtain ⟨cvR0P, mI0P, rP0P, rules0P⟩ := r0P
    dsimp only at hR0 hrun
    simp only [shapeOfSplitP]
    generalize hTsL : cvT0 :: cvTs' = cvTs at hTs hrun
    generalize hrsL : (cvR0, mI0, rP0, rules0) :: rs' = rs at hrs hrun
    generalize hTsP : cvT0P :: cvTsP' = cvTsP at hTs ⊢
    generalize hrsP : (cvR0P, mI0P, rP0P, rules0P) :: rsP' = rsP at hrs ⊢
    have hlenT : cvTs.length = cvTsP.length := (ConLeche.option_mapM_length hTs).symm
    have hlenC : cs.length = csP.length := denoteCtors3_length hcs
    obtain ⟨cnt, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hcnt⟩ := blockMemberCounts?_spec nPd cvTs.length cs.length
      (cvTs.map (·.name)) (cvTsP.map (·.name)) rs rsP 0 cvTs cvTsP s₀ s1 cnt hok
      ⟨cvNames_go hTs, hrs, hTs⟩ k1
    simp only [RV] at hcnt
    subst hcnt
    have hcnt' : ConLeche.blockMemberCounts? nPd cvTs.length cs.length
        (cvTsP.map (·.name)) rsP 0 cvTsP = ConLeche.blockMemberCounts? nPd cvTsP.length
        csP.length (cvTsP.map (·.name)) rsP 0 cvTsP := by rw [hlenT, hlenC]
    rw [hcnt'] at z1
    cases hcntP : ConLeche.blockMemberCounts? nPd cvTsP.length csP.length
        (cvTsP.map (·.name)) rsP 0 cvTsP with
    | none =>
      rw [hcntP] at z1
      obtain ⟨rfl, rfl⟩ := pureOk z1
      exact ⟨p1, rfl⟩
    | some nIdxs =>
    rw [hcntP] at z1
    dsimp only at z1 ⊢
    obtain ⟨reserved, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hres⟩ := reservedBasisNames_pstep p1.ok (hc.pins.mono p1.ext p1.pins) k2
    have q2 : PStep s₀ s2 := p1.trans p2
    have x2 := q2.ext
    have hwf := q2.ok.wf
    have hlps := denoteNListE_ext x2 _ _ (denoteCV_lps hT0)
    have E1 : (cvTs.all fun c => !reserved.contains c.name && c.levelParams == cvT0.levelParams)
        = (cvTsP.all fun c => (reservedBasisNames.contains c.name == false) &&
            c.levelParams == cvT0P.levelParams) :=
      all_mapM_eq (fun x y h => by
        rw [not_eq_beq_false (denoteNList_contains hwf _ _ hres _ _ (denoteCV_name h)),
          beq_nhandleList_eq hwf (denoteCV_lps h) hlps])
        cvTs cvTsP (mapM_option_ext (fun a b h => denoteCV_ext h x2) _ _ hTs)
    have E2 : (rs.all fun r => !reserved.contains r.1.name)
        = (rsP.all fun r => reservedBasisNames.contains r.1.name == false) :=
      all_mapM_eq (fun x y h => by
        rw [not_eq_beq_false (denoteNList_contains hwf _ _ hres _ _
          (denoteCV_name (dRec4_inv h).1))])
        rs rsP (mapM_option_ext (fun a b h => dRec4_ext x2 a b h) _ _ hrs)
    have E3 : (cs.all fun c => c.2.1 == nPd && c.1.levelParams == cvT0.levelParams &&
          !reserved.contains c.1.name)
        = (csP.all fun c => c.2.1 == nPd && c.1.levelParams == cvT0P.levelParams &&
          reservedBasisNames.contains c.1.name == false) :=
      all_ctors3_eq (fun cv a b cvP h => by
        simp only
        rw [not_eq_beq_false (denoteNList_contains hwf _ _ hres _ _ (denoteCV_name h)),
          beq_nhandleList_eq hwf (denoteCV_lps h) hlps])
        cs csP (denoteCtors3_ext x2 _ _ hcs)
    rw [E1, E2, E3, all_and_split] at z2
    have hB : ∀ a b c d : Bool, (((a && c) && b) && d) = (((a && b) && c) && d) := by decide
    rw [hB] at z2
    split at z2
    case isFalse hcnd =>
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨q2, ?_⟩
      show _ = none
      rw [if_neg hcnd]
    case isTrue hcnd =>
    rw [if_pos hcnd]
    obtain ⟨o, s3, k3, z3⟩ := bindOk z2
    obtain ⟨hs3, hbp⟩ := stripPis_pstep q2.ok (denote_ext (denoteCV_type hT0) x2) k3
    rw [hs3] at z3
    have hT0' := denoteCV_ext hT0 x2
    have hR0' := denoteCV_ext hR0 x2
    have hTs' := mapM_option_ext (fun a b h => denoteCV_ext h x2) _ _ hTs
    have hcs' := denoteCtors3_ext x2 _ _ hcs
    have hrs' := mapM_option_ext (fun a b h => dRec4_ext x2 a b h) _ _ hrs
    have hp2 := hc.pins.mono q2.ext q2.pins
    cases o with
    | none =>
      obtain ⟨y, s4, k4, z4⟩ := bindOk z3
      obtain ⟨hs4, hy⟩ := zeroLevel_run hp2 k4
      rw [hs4] at z4
      have hyP : denoteL s2.store.ls y = some (resSortOfP cvT0P.type (nPd + nIdxs.headD 0)) := by
        simp only [resSortOfP, stripPis_none hbp]; exact hy
      exact shapeTail_run nPd cvT0 cvR0 cvT0P cvR0P cvTs cvTsP cs csP rs rsP nIdxs y hc q2
        hT0' hR0' hTs' hcs' hrs' hyP z4
    | some qq =>
      obtain ⟨bs, e⟩ := qq
      obtain ⟨xs, x, hsp, -, hx⟩ := denoteBP_some hbp
      dsimp only at z3
      obtain ⟨v, s4, k4, z4⟩ := bindOk z3
      obtain ⟨hs4, hview⟩ := view_run k4
      rw [hs4] at z4
      have hbv : denoteEView s2.store v = some x := by
        rw [← denoteE_view_eq q2.ok.wf hview]; exact hx
      cases v
      case sort u =>
        obtain ⟨l, rfl, hl⟩ := denote_sort_inv q2.ok.wf hview hx
        obtain ⟨y, s5, k5, z5⟩ := bindOk z4
        obtain ⟨hyu, hs5⟩ := pureOk k5
        rw [hs5] at z5
        have hyP : denoteL s2.store.ls y = some (resSortOfP cvT0P.type (nPd + nIdxs.headD 0)) := by
          rw [hyu]; simp only [resSortOfP, hsp]; exact hl
        exact shapeTail_run nPd cvT0 cvR0 cvT0P cvR0P cvTs cvTsP cs csP rs rsP nIdxs y hc q2
          hT0' hR0' hTs' hcs' hrs' hyP z5
      all_goals
        (have hns := ExprOps.denoteEView_not_sort hbv (by simp)
         obtain ⟨y, s5, k5, z5⟩ := bindOk z4
         obtain ⟨hs5, hy⟩ := zeroLevel_run hp2 k5
         rw [hs5] at z5
         have hyP : denoteL s2.store.ls y =
             some (resSortOfP cvT0P.type (nPd + nIdxs.headD 0)) := by
           simp only [resSortOfP, hsp]
           cases x <;> first | exact hy | exact absurd rfl (hns _)
         exact shapeTail_run nPd cvT0 cvR0 cvT0P cvR0P cvTs cvTsP cs csP rs rsP nIdxs y hc q2
           hT0' hR0' hTs' hcs' hrs' hyP z5)

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:444-449 blockParts?
**THE DISPATCH'S RECOGNISER** — `checkBlock` against `checkShapeless` routes
on this, so its two-sidedness (`ROp`) is the soundness of the route choice.
CORE grade, for `blockShape?`'s reason. -/
theorem blockParts?_spec {μ : CheckMode} {env : Env} (fe : IFEnv) (nP : Nat)
    (block : List IConstantInfo) (b : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some b)
      (Arena.blockParts? nP block)
      (ROp (fun q st p => dParts st p = some q) (ConLeche.blockParts? nP b)) := by
  intro s₀ s' r hok hb hrun
  simp only [Arena.blockParts?] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hrel⟩ := blockShape?_run nP block b s₀ s₁ o hok hb h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨p1.toCore hok, ?_⟩
    show ConLeche.blockParts? nP b = none
    simp only [ConLeche.blockParts?, show ConLeche.blockShape? nP b = none from hrel]
  | some p =>
    obtain ⟨q, hq, hpq⟩ := hrel
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨p1.toCore hok, ⟨q⟩, by simp only [ConLeche.blockParts?, hq], ?_⟩
    simp only [dParts, hpq, Option.map_some]

end ConRon.Bridge.Inductives
