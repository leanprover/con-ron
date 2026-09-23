/-
# `ConRon.Bridge.Inductives.NativeParts` — Theorem 1 for the generated recursor

`Arena/Inductives/NativeParts.lean`'s thirty-three twins against
`ConLeche/Kernel/Inductives/NativeParts.lean`: the positivity classification,
the recursor type and right-hand sides the install FABRICATES and compares the
stream's against, the rule checks and the two recognisers.

**All PURE grade.**  Nothing here calls the knot; `recPositivity` and
`recFamOk` walk handles and `mentionsConst` them, and the generators intern.

## The five higher-order arguments, and how their statements read

Task #97d-2's deviation 3 removed five function arguments con-leche passes,
because DESIGN §3.4 forbids a closure.  Three of them are in this module:

* `structRuleBodyR`'s and `structIhPis`' `teleOf`/`idxOf` became the
  constructor type `cty` and the two counts, with `structFieldTeleOf` /
  `structFieldIdxOf` called INSIDE;
* `nativeRulesOk` carries the same substitution one level up.

So each of those statements is a `…_congr`-shaped one in task #97-P3-0 §2's
sense: the twin is compared with con-leche's function AT the two concrete
readers, `fun i => ConLeche.structFieldTeleOf ctyP nP nF i` and its sibling.
That instantiation is the whole content of the deviation, and stating it is
what discharges it.

## `piBinders` has fuel and con-leche's does not

`Expr.piBinders` is structural on the `Expr`; the twin cannot be, because a
handle has no structural measure, so it takes `coreWalkFuel`.  Partial
correctness makes this free: `PSpec` assumes the run ACCEPTED, and a run that
exhausted its fuel `fail`ed.  The same applies to `recPositivity`.
-/
import ConRon.Bridge.Inductives.SumParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The positivity classification -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:78-87 recFamOk
Is `e` the family at the parameter variables followed by `nIdx` index
expressions none of which mentions the block?  Official's `is_valid_ind_app`.

`sorry`: `Bridge/ExprOps/Spine.lean`'s `getAppSpine` spec, `structFam_spec`
and `mentionsConst_spec`. -/
theorem recFamOk_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx o : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st e = some eP)
      (Arena.recFamOk T lps nP nIdx o e)
      (RV (ConLeche.recFamOk TP lpsP nP nIdx o eP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:89-111 recPositivity
The field domain's kind, walking under its own binders.

`sorry`: a fuel induction whose `.forallE` arm is `Bridge/Rel.lean`'s
`forallE` inversion and whose leaf arm is `recFamOk_spec` + `mentionsConst_spec`. -/
theorem recPositivity_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx o fuel : Nat) (h : EIdx) (hP : Expr)
    (k : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st h = some hP)
      (Arena.recPositivity T lps nP nIdx o fuel h k)
      (RK (ConLeche.recPositivity TP lpsP nP nIdx o hP k)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:113-116 recFieldKind
The entry at `k = 0`.

`sorry`: `recPositivity_spec`. -/
theorem recFieldKind_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx o : Nat) (dom : EIdx) (domP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st dom = some domP)
      (Arena.recFieldKind T lps nP nIdx o dom)
      (RK (ConLeche.recFieldKind TP lpsP nP nIdx o domP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
One constructor's field kinds, or `none` when its residual is not the family.

`sorry`: the telescope peel (`Bridge/ExprOps/TelescopeF.lean`) and
`recFieldKind_spec` at each domain. -/
theorem recCtorKinds_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat) (c : IConstantVal × Nat)
    (cP : ConstantVal × Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        Frontend.denoteCV st c.1 = some cP.1 ∧ c.2 = cP.2)
      (Arena.recCtorKinds T lps nP nIdx c)
      (ROp RKs (ConLeche.recCtorKinds TP lpsP nP nIdx cP)) := by
  sorry

/-! ## The telescope readers -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:147-154 Expr.piBinders
Peel `fuel` Π binders; the twin's fuel is invisible under partial correctness
(see the module note).

**CLOSED** (task #97-P3-Ind round 2): a fuel induction over
`Bridge/Rel.lean`'s `forallE` inversion, with the nine arms that are not a
binder stopping on both sides (`Bridge/Inductives/Rel.lean`'s
`piSortTeleLen?_spec` has the same ten-way shape). -/
theorem piBinders_spec : ∀ (fuel : Nat) (h : EIdx) (hP : Expr),
    PSpec (fun st => denoteE st h = some hP)
      (Arena.piBinders fuel h)
      (fun st r => denoteBinders st r.1 = some (Expr.piBinders hP).1 ∧
        denoteE st r.2 = some (Expr.piBinders hP).2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piBinders] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piBinders] at hrun
    obtain ⟨v, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨hs1, hw⟩ := view_run h1
    rw [hs1] at h2
    have hde : denoteEView s₀.store v = some hP := by
      rw [denoteE_view_eq hok.wf hw] at hd; exact hd
    cases v
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hb⟩ := denote_forallE_inv hok.wf hw hd
      obtain ⟨q, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨hstep, hq1, hq2⟩ := ih b eb s₀ s₂ q hok hb h3
      obtain ⟨rfl, rfl⟩ := pureOk h4
      refine ⟨hstep, ?_, ?_⟩
      · simp only [Expr.piBinders, denoteBinders,
          denote_ext hty hstep.ext, hq1]
      · simpa only [Expr.piBinders] using hq2
    all_goals
      (obtain ⟨rfl, rfl⟩ := pureOk h2
       refine ⟨PStep.refl hok, ?_, ?_⟩
       · simp only [denoteEView] at hde
         first
         | (obtain ⟨x, y, z, _, _, _, rfl⟩ := opt3_eq_some_iff.mp hde; rfl)
         | (obtain ⟨x, y, _, _, rfl⟩ := opt2_eq_some_iff.mp hde; rfl)
         | (obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp hde; rfl)
         | (obtain rfl := Option.some.inj hde; rfl)
       · simp only [denoteEView] at hde
         first
         | (obtain ⟨x, y, z, _, _, _, rfl⟩ := opt3_eq_some_iff.mp hde
            simpa only [Expr.piBinders] using hd)
         | (obtain ⟨x, y, _, _, rfl⟩ := opt2_eq_some_iff.mp hde
            simpa only [Expr.piBinders] using hd)
         | (obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.mp hde
            simpa only [Expr.piBinders] using hd)
         | (obtain rfl := Option.some.inj hde
            simpa only [Expr.piBinders] using hd))

/-! ### THE `default` TRAP — `i < nF` is part of both statements

Task #97-P3-Ind round 3 flagged these two for the next round to CHECK before
proving, and the check says the statements were FALSE.  Both twins read
`(cbs.getD (nP + i) default).1`.  On the arena side that `default` is
`(default : EIdx × BinderMeta)`, i.e. the handle `Idx.ofWord 0` — tag 0, the
persistent tier, slot 0 — and on con-leche's it is
`(default : Expr × BinderMeta)`, i.e. `Expr.bvar 0`.  **Nothing relates
them**, and `StateOK` says nothing about what persistent expression slot 0
holds: at a state whose slot 0 is an application, `structFieldIdxOf` answers
that application's argument spine dropped by `nP` where con-leche answers
`[]` (`(Expr.bvar 0).getAppArgs = []`), and at one whose slot 0 is a `∀`,
`structFieldTeleOf` answers a non-empty telescope where con-leche answers
`[]`.  `nP = 0`, `nF = 0`, `i = 0` is a two-line witness for either.

The fallback is taken exactly when `nP + i ≥ cbs.length`, and
`ConLeche.Expr.stripPis_length` says `cbs.length = nP + nF` on the accepting
branch — so **`i < nF` is exactly the hypothesis that keeps both statements on
real data**, and it is a hypothesis the twins' only callers have: they are
called at `i ∈ recIdx` and `recIdx = recIdxOf ks` is a sublist of
`List.range ks.length`.  `structRuleBodyR_spec` and `structIhPis_spec` carry
it on as `∀ i ∈ recIdx, i < nF`; see their statements. -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:156-161 structFieldTeleOf
Field `i`'s own Π-telescope.

**PROVED** (round 4), at the corrected statement: `stripPis_pstep` with
`denoteBP_someB` (the binder half of the inversion, new in `Rel.lean`),
`denoteBinders_getD` at the position the bound licenses, and
`piBinders_spec`. -/
theorem structFieldTeleOf_spec (cty : EIdx) (ctyP : Expr) (nP nF i : Nat)
    (hi : i < nF) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structFieldTeleOf cty nP nF i)
      (RB (ConLeche.structFieldTeleOf ctyP nP nF i)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.structFieldTeleOf] at hrun
  obtain ⟨sp, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hd h1
  cases sp with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨PStep.refl hok, ?_⟩
    simp only [RB, ConLeche.structFieldTeleOf, stripPis_none hbp, denoteBinders]
  | some p =>
    obtain ⟨cbs, cbody⟩ := p
    obtain ⟨cbsP, bodyP, hsp, hcbs, _hbody⟩ := denoteBP_someB hbp
    have hlen : cbsP.length = nP + nF := ConLeche.Expr.stripPis_length _ hsp
    have hlen2 : cbs.length = cbsP.length := denoteBinders_length hcbs
    have hk : nP + i < cbs.length := by omega
    obtain ⟨pb, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨pbs, pbody⟩ := pb
    obtain ⟨hstep, hb1, _hb2⟩ :=
      piBinders_spec Arena.coreWalkFuel _ _ _ s₂ (pbs, pbody) hok
        (denoteBinders_getD hcbs hk) h3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨hstep, ?_⟩
    simp only [RB, ConLeche.structFieldTeleOf, hsp]
    exact hb1

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:163-169 structFieldIdxOf
Field `i`'s index arguments.

**PROVED** (round 4), at the corrected statement: `structFieldTeleOf_spec`'s
route to the field domain, then `getAppArgs_run` and `denoteEList_drop`. -/
theorem structFieldIdxOf_spec (cty : EIdx) (ctyP : Expr) (nP nF i : Nat)
    (hi : i < nF) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structFieldIdxOf cty nP nF i)
      (REL (ConLeche.structFieldIdxOf ctyP nP nF i)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.structFieldIdxOf] at hrun
  obtain ⟨sp, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hd h1
  cases sp with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨PStep.refl hok, ?_⟩
    simp only [REL, ConLeche.structFieldIdxOf, stripPis_none hbp,
      Frontend.denoteEList]
  | some p =>
    obtain ⟨cbs, cbody⟩ := p
    obtain ⟨cbsP, bodyP, hsp, hcbs, _hbody⟩ := denoteBP_someB hbp
    have hlen : cbsP.length = nP + nF := ConLeche.Expr.stripPis_length _ hsp
    have hlen2 : cbs.length = cbsP.length := denoteBinders_length hcbs
    have hk : nP + i < cbs.length := by omega
    obtain ⟨pb, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨pbs, pbody⟩ := pb
    obtain ⟨hstep, _hb1, hb2⟩ :=
      piBinders_spec Arena.coreWalkFuel _ _ _ s₂ (pbs, pbody) hok
        (denoteBinders_getD hcbs hk) h3
    obtain ⟨args, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨rfl, hargs⟩ := getAppArgs_run hstep.ok hb2 h5
    obtain ⟨rfl, rfl⟩ := pureOk h6
    refine ⟨hstep, ?_⟩
    simp only [REL, ConLeche.structFieldIdxOf, hsp]
    exact denoteEList_drop hargs nP

/-! ## The three pure record operations

`recIdxOf`, `NativeParts.complete` and `NativeParts.withKinds` touch no term
(task #97d-2's deviation 8), so their statements are plain equations rather
than `PSpec`s — and all three are CLOSED. -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:171-175 recIdxOf
The positions of the recursive fields.  The twin's `RecFieldKind` is
con-leche's under `kindOf`, and `recIdxOf` reads nothing else. -/
theorem recIdxOf_spec (ks : List Arena.RecFieldKind) :
    Arena.recIdxOf ks = ConLeche.recIdxOf (ks.map kindOf) := by
  simp only [Arena.recIdxOf, ConLeche.recIdxOf, List.length_map]
  congr 1
  funext i
  cases h : ks[i]?  with
  | none =>
    have : (ks.map kindOf)[i]? = none := by simp [h]
    simp only [List.getD, h, this, Option.getD]
    rfl
  | some k =>
    have : (ks.map kindOf)[i]? = some (kindOf k) := by simp [h]
    simp only [List.getD, h, this, Option.getD]
    cases k <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:194-199 NativeParts.complete
The record completed by the former's stage: the shape moves, the kinds and the
pin bit stay. -/
theorem complete_spec {st : EStore} {p₀ : Arena.NativeParts}
    {q₀ : ConLeche.NativeParts} {p₁ : Arena.InductiveShape}
    {q₁ : ConLeche.InductiveShape} (h₀ : PartsRel st p₀ q₀)
    (h₁ : ShapeRel st p₁ q₁) :
    PartsRel st (p₀.complete p₁) (q₀.complete q₁) :=
  ⟨h₁, h₀.kinds, h₀.recPinned⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:616-622 NativeParts.withKinds
The record with the classification's kinds written in. -/
theorem withKinds_spec {st : EStore} {p : Arena.NativeParts}
    {q : ConLeche.NativeParts} {ks : List (List Arena.RecFieldKind)}
    (h : PartsRel st p q) :
    PartsRel st (p.withKinds ks) (q.withKinds (ks.map (·.map kindOf))) :=
  ⟨h.shape, rfl, h.recPinned⟩

/-! ## The generated recursor -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:230-235 structRecPrefixAt
The recursor's leading spine `p⃗ motive m⃗` as seen from under the fields.

**CLOSED** (task #97-P3-Ind round 2): `structPsAt_spec` twice,
`internBVarE_run` for the motive, and `denoteEList_append` for the two
joins. -/
theorem structRecPrefixAt_spec (nP n nF e : Nat) :
    PSpec PT (Arena.structRecPrefixAt nP n nF e)
      (REL (ConLeche.structRecPrefixAt nP n nF e)) := by
  intro s₀ s' r hok _ hrun
  simp only [Arena.structRecPrefixAt] at hrun
  obtain ⟨ps, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep1, hps⟩ :=
    structPsAt_spec (e + nF + n + 1) nP s₀ s₁ ps hok trivial h1
  obtain ⟨motive, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hstep2, hmv⟩ := internBVarE_run hstep1.ok h3
  obtain ⟨minors, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨hstep3, hmn⟩ :=
    structPsAt_spec (e + nF) n s₂ s₃ minors hstep2.ok trivial h5
  obtain ⟨rfl, rfl⟩ := pureOk h6
  refine ⟨hstep1.trans (hstep2.trans hstep3), ?_⟩
  have hmv' : Frontend.denoteEList s'.store [motive]
      = some [Expr.bvar (e + nF + n)] := by
    simp only [Frontend.denoteEList, denote_ext hmv hstep3.ext]
  have hps' := denoteEList_ext (hstep2.ext.trans hstep3.ext) _ _ hps
  simp only [ConLeche.structRecPrefixAt, ConLeche.structPsAt] at *
  exact denoteEList_append (denoteEList_append hps' hmv') hmn

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:237-244 structIdxAt
A recursive field's index expression relocated to the rule frame.

**CLOSED** (task #97-P3-Ind round 5), on the conjunct round 4 §R4.4 asked the
`ExprOps` tier for: `LiftSpec` now states `BMExt`, so a `PSpec`-grade twin
that lifts can produce a `PStep`.  Two `liftFast_pstep`s.  **This is group 3's
gateway** — `structTeleAt`, `structIhApp`, `structRuleBodyR`, `structIhPis`,
`structMinorTyR`, `structMinorsPisR`, `structMinorsLamsR`, `structRecTyR` and
`structRecRhsR` all wait on it and on nothing else of another tier. -/
theorem structIdxAt_spec (nF o i l m : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.structIdxAt nF o i l m e)
      (RE (ConLeche.structIdxAt nF o i l m eP)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.structIdxAt] at hrun
  obtain ⟨a, s1, k1, hz⟩ := bindOk hrun
  obtain ⟨p1, ha⟩ := liftFast_pstep hok hd k1
  obtain ⟨p2, hr⟩ := liftFast_pstep p1.ok ha hz
  exact ⟨p1.trans p2, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:246-252 structTeleAt
A field's telescope relocated, with a fresh `PropWhen` on each binder.

`sorry`: `structIdxAt_spec` at each domain, a list map. -/
theorem structTeleAt_spec (nF o i l : Nat) (pw : PropWhen)
    (tele : List (EIdx × BinderMeta)) (teleP : List (Expr × BinderMeta)) :
    PSpec (fun st => denoteBinders st tele = some teleP)
      (Arena.structTeleAt nF o i l pw tele)
      (RB (ConLeche.structTeleAt nF o i l pw teleP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:254-255 structTeleVars
`bvarsDesc m`; con-leche's is the same `List.range` map.

**CLOSED** (task #97-P3-Ind round 2): `bvarsDesc_spec` and
`bvarRange_congr`. -/
theorem structTeleVars_spec (m : Nat) :
    PSpec PT (Arena.structTeleVars m) (REL (ConLeche.structTeleVars m)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hstep, hr⟩ := bvarsDesc_spec m s₀ s' r hok hp hrun
  refine ⟨hstep, ?_⟩
  have : ConLeche.structTeleVars m = ConLeche.structPsAt 0 m := by
    simp only [ConLeche.structTeleVars, ConLeche.structPsAt]
    exact bvarRange_congr (fun j => by omega)
  rw [this]
  exact hr

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:257-260 Expr.mkPisOf
Close a body under a telescope of Π binders.

**CLOSED** (task #97-P3-Ind round 2): a list induction over
`internForallEE_run`. -/
theorem mkPisOf_spec : ∀ (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (body : EIdx) (bodyP : Expr),
    PSpec (fun st => denoteBinders st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.mkPisOf bs body) (RE (Expr.mkPisOf bsP bodyP)) := by
  intro bs
  induction bs with
  | nil =>
    intro bsP body bodyP s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    simp only [denoteBinders, Option.some.injEq] at hbs
    subst hbs
    simp only [Arena.mkPisOf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, hbody⟩
  | cons a as ih =>
    intro bsP body bodyP s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    obtain ⟨ty, mt⟩ := a
    simp only [denoteBinders] at hbs
    cases hty : denoteE s₀.store ty with
    | none => rw [hty] at hbs; simp at hbs
    | some tyP =>
      cases has : denoteBinders s₀.store as with
      | none => rw [hty, has] at hbs; simp at hbs
      | some rest =>
        rw [hty, has] at hbs
        obtain rfl := Option.some.inj hbs
        simp only [Arena.mkPisOf] at hrun
        obtain ⟨x, s₁, h1, h2⟩ := bindOk hrun
        obtain ⟨hstep1, hx⟩ := ih rest body bodyP s₀ s₁ x hok ⟨has, hbody⟩ h1
        obtain ⟨hstep2, hr⟩ :=
          internForallEE_run hstep1.ok (denote_ext hty hstep1.ext) hx h2
        exact ⟨hstep1.trans hstep2, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:261-263 Expr.mkLamsOf
The same with `.lam`.

**CLOSED** (task #97-P3-Ind round 2): `mkPisOf_spec`'s proof with
`internLamE_run`. -/
theorem mkLamsOf_spec : ∀ (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (body : EIdx) (bodyP : Expr),
    PSpec (fun st => denoteBinders st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.mkLamsOf bs body) (RE (Expr.mkLamsOf bsP bodyP)) := by
  intro bs
  induction bs with
  | nil =>
    intro bsP body bodyP s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    simp only [denoteBinders, Option.some.injEq] at hbs
    subst hbs
    simp only [Arena.mkLamsOf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, hbody⟩
  | cons a as ih =>
    intro bsP body bodyP s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    obtain ⟨ty, mt⟩ := a
    simp only [denoteBinders] at hbs
    cases hty : denoteE s₀.store ty with
    | none => rw [hty] at hbs; simp at hbs
    | some tyP =>
      cases has : denoteBinders s₀.store as with
      | none => rw [hty, has] at hbs; simp at hbs
      | some rest =>
        rw [hty, has] at hbs
        obtain rfl := Option.some.inj hbs
        simp only [Arena.mkLamsOf] at hrun
        obtain ⟨x, s₁, h1, h2⟩ := bindOk hrun
        obtain ⟨hstep1, hx⟩ := ih rest body bodyP s₀ s₁ x hok ⟨has, hbody⟩ h1
        obtain ⟨hstep2, hr⟩ :=
          internLamE_run hstep1.ok (denote_ext hty hstep1.ext) hx h2
        exact ⟨hstep1.trans hstep2, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:265-277 structIhApp
The inductive-hypothesis application inside a minor premise.

`sorry`: `structRecPrefixAt_spec`, `structTeleVars_spec`, `structIdxAt_spec`
and `mkAppN`'s spec. -/
theorem structIhApp_spec (recC : NIdx) (recCP : ConLeche.Name) (rlvls : LsIdx)
    (rlvlsP : List Level) (pw : PropWhen) (nP n nF i : Nat)
    (tele : List (EIdx × BinderMeta)) (teleP : List (Expr × BinderMeta))
    (idx : List EIdx) (idxP : List Expr) :
    PSpec (fun st => denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧
        denoteBinders st tele = some teleP ∧
        Frontend.denoteEList st idx = some idxP)
      (Arena.structIhApp recC rlvls pw nP n nF i tele idx)
      (RE (ConLeche.structIhApp recCP rlvlsP pw nP n nF i teleP idxP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:279-288 structRuleBodyR
The rule's right-hand-side body.  **Task #97d-2's deviation 3**: con-leche
takes `teleOf`/`idxOf` as FUNCTIONS and the twin takes the constructor type and
calls the two readers itself, so the statement compares the twin with
con-leche at those two readers — which is what discharges the deviation.

`sorry`: `structFieldTeleOf_spec`, `structFieldIdxOf_spec`, `structIhApp_spec`
and `mkAppN`'s spec. -/
theorem structRuleBodyR_spec (recC : NIdx) (recCP : ConLeche.Name)
    (rlvls : LsIdx) (rlvlsP : List Level) (pw : PropWhen) (nP n nF j : Nat)
    (recIdx : List Nat) (cty : EIdx) (ctyP : Expr)
    (hri : ∀ i ∈ recIdx, i < nF) :
    PSpec (fun st => denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧ denoteE st cty = some ctyP)
      (Arena.structRuleBodyR recC rlvls pw nP n nF j recIdx cty)
      (RE (ConLeche.structRuleBodyR recCP rlvlsP pw nP n nF j recIdx
        (fun i => ConLeche.structFieldTeleOf ctyP nP nF i)
        (fun i => ConLeche.structFieldIdxOf ctyP nP nF i))) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:290-305 structIhPis
The inductive-hypothesis binders in front of a minor premise's body.  The same
deviation, the same instantiation; note con-leche's `nP` is not a parameter of
its version (it reads it through `teleOf`).

`sorry`: a list induction over `structTeleAt_spec`, `structIhApp_spec` and
`mkPisOf_spec`. -/
theorem structIhPis_spec (nF o nP : Nat) (pw : PropWhen) (cty : EIdx)
    (ctyP : Expr) (is : List Nat) (l : Nat) (body : EIdx) (bodyP : Expr)
    (his : ∀ i ∈ is, i < nF) :
    PSpec (fun st => denoteE st cty = some ctyP ∧
        denoteE st body = some bodyP)
      (Arena.structIhPis nF o nP pw cty is l body)
      (RE (ConLeche.structIhPis nF o pw
        (fun i => ConLeche.structFieldTeleOf ctyP nP nF i)
        (fun i => ConLeche.structFieldIdxOf ctyP nP nF i) is l bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
One minor premise's type.

`sorry`: `replacePisPw_spec`, `structIhPis_spec`, `structCtorSpineAt_spec`
and `structRecPrefixAt_spec`. -/
theorem structMinorTyR_spec (C : NIdx) (CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF o : Nat) (pw : PropWhen) (cty : EIdx)
    (ctyP : Expr) (recIdx : List Nat) (hri : ∀ i ∈ recIdx, i < nF) :
    PSpec (fun st => denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st cty = some ctyP)
      (Arena.structMinorTyR C lps nP nF o pw cty recIdx)
      (ROp RE (ConLeche.structMinorTyR CP lpsP nP nF o pw ctyP recIdx)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:322-330 structMinorsPisR
All the minor premises as Π binders in front of a body.

`sorry`: a list induction over `structMinorTyR_spec` and `internE_spec`. -/
theorem structMinorsPisR_spec (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP : Nat) (pw : PropWhen) (cs : List (NIdx × Nat × EIdx × List Nat))
    (csP : List (ConLeche.Name × Nat × Expr × List Nat)) (o : Nat)
    (body : EIdx) (bodyP : Expr)
    (hcs : ∀ c ∈ csP, ∀ i ∈ c.2.2.2, i < c.2.1) :
    PSpec (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors4 st cs = some csP ∧ denoteE st body = some bodyP)
      (Arena.structMinorsPisR lps nP pw cs o body)
      (ROp RE (ConLeche.structMinorsPisR lpsP nP pw csP o bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:332-339 structMinorsLamsR
The same as λ binders.

`sorry`: `structMinorsPisR_spec`'s argument with `.lam`. -/
theorem structMinorsLamsR_spec (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP : Nat) (pw : PropWhen) (cs : List (NIdx × Nat × EIdx × List Nat))
    (csP : List (ConLeche.Name × Nat × Expr × List Nat)) (o : Nat)
    (body : EIdx) (bodyP : Expr)
    (hcs : ∀ c ∈ csP, ∀ i ∈ c.2.2.2, i < c.2.1) :
    PSpec (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors4 st cs = some csP ∧ denoteE st body = some bodyP)
      (Arena.structMinorsLamsR lps nP pw cs o body)
      (ROp RE (ConLeche.structMinorsLamsR lpsP nP pw csP o bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:341-362 structRecTyR
**THE GENERATED RECURSOR'S TYPE** — the term the install compares the stream's
recursor against, so this statement is what makes "the recursor is the
generated one" mean the same on both sides.

`sorry`: `structMotiveTyI_spec`, `structMinorsPisR_spec`,
`structElimLevel_spec`, `structFamI_spec` and `replacePisPw_spec`. -/
theorem structRecTyR_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ttyP : Expr)
    (ctors : List (NIdx × Nat × EIdx × List Nat))
    (ctorsP : List (ConLeche.Name × Nat × Expr × List Nat))
    (hcs : ∀ c ∈ ctorsP, ∀ i ∈ c.2.2.2, i < c.2.1) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteCtors4 st ctors = some ctorsP)
      (Arena.structRecTyR T lps elim large nP nIdx tty ctors)
      (ROp RE (ConLeche.structRecTyR TP lpsP elimP large nP nIdx ttyP ctorsP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:364-386 structRecRhsR
**THE GENERATED RULE'S RIGHT-HAND SIDE**, constructor `j`'s.

`sorry`: `structRecTyR_spec`'s pieces plus `structMinorsLamsR_spec`,
`structRuleBodyR_spec` and `pisToLamsPw_spec`. -/
theorem structRecRhsR_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ttyP : Expr)
    (ctors : List (NIdx × Nat × EIdx × List Nat))
    (ctorsP : List (ConLeche.Name × Nat × Expr × List Nat)) (recC : NIdx)
    (recCP : ConLeche.Name) (rlvls : LsIdx) (rlvlsP : List Level) (j : Nat)
    (hcs : ∀ c ∈ ctorsP, ∀ i ∈ c.2.2.2, i < c.2.1) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteCtors4 st ctors = some ctorsP ∧
        denoteN st.ns recC = some recCP ∧ denoteLs st.lss rlvls = some rlvlsP)
      (Arena.structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (ROp RE (ConLeche.structRecRhsR TP lpsP elimP large nP nIdx ttyP ctorsP
        recCP rlvlsP j)) := by
  sorry

/-! ## The four-tuple and the rule checks -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:388-392 nativeCtors4
The generators' input: each constructor's name, field count, type and
recursive-field positions.  Pure on both sides.

`sorry`: a list zip induction over `recIdxOf_spec` (closed above) and the
`denoteCtors`/`denoteCtors4` clauses. -/
theorem nativeCtors4_spec {st : EStore} :
    ∀ (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat))
      (kinds : List (List Arena.RecFieldKind)),
    denoteCtors st ctorsA = some ctorsAP →
    denoteCtors4 st (Arena.nativeCtors4 ctorsA kinds)
      = some (ConLeche.nativeCtors4 ctorsAP (kinds.map (·.map kindOf))) := by
  intro ctorsA
  induction ctorsA with
  | nil =>
    intro ctorsAP kinds h
    simp only [denoteCtors, Option.some.injEq] at h
    subst h
    simp only [Arena.nativeCtors4, ConLeche.nativeCtors4, List.zipWith_nil_left,
      denoteCtors4]
  | cons a as ih =>
    intro ctorsAP kinds h
    obtain ⟨cv, n⟩ := a
    simp only [denoteCtors] at h
    cases hcv : Frontend.denoteCV st cv with
    | none => rw [hcv] at h; simp at h
    | some c =>
      cases has : denoteCtors st as with
      | none => rw [hcv, has] at h; simp at h
      | some rs =>
        rw [hcv, has] at h
        obtain rfl := Option.some.inj h
        cases kinds with
        | nil =>
          simp only [Arena.nativeCtors4, ConLeche.nativeCtors4,
            List.zipWith_nil_right, List.map_nil, denoteCtors4]
        | cons k ks =>
          have hih := ih rs ks has
          simp only [Arena.nativeCtors4, ConLeche.nativeCtors4,
            recIdxOf_spec] at hih ⊢
          simp only [List.map_cons, List.zipWith_cons_cons, denoteCtors4,
            denoteCV_name hcv, denoteCV_type hcv, hih]

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
The stream rule's λ prefix is the generated one.

`sorry`: `stripLams`' spec and the structural comparison through
`denoteE_inj`. -/
theorem nativeRulePrefixOk_spec (recTy : EIdx) (recTyP : Expr)
    (nP n j nF : Nat) (rhs : EIdx) (rhsP : Expr) :
    PSpec (fun st => denoteE st recTy = some recTyP ∧
        denoteE st rhs = some rhsP)
      (Arena.nativeRulePrefixOk recTy nP n j nF rhs)
      (RV (ConLeche.nativeRulePrefixOk recTyP nP n j nF rhsP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
**The stream's rules are the generated ones**, constructor by constructor.

`sorry`: `structRecRhsR_spec`, `nativeRulePrefixOk_spec` and
`nativeCtors4_spec`, over a list induction. -/
theorem nativeRulesOk_spec (recC : NIdx) (recCP : ConLeche.Name)
    (rlvls : LsIdx) (rlvlsP : List Level) (pw : PropWhen) (nP n : Nat)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (kinds : List (List Arena.RecFieldKind)) (rhss : List EIdx)
    (rhssP : List Expr) (recTy : EIdx) (recTyP : Expr) :
    PSpec (fun st => denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧ denoteCtors st cs = some csP ∧
        Frontend.denoteEList st rhss = some rhssP ∧
        denoteE st recTy = some recTyP)
      (Arena.nativeRulesOk recC rlvls pw nP n cs kinds rhss recTy)
      (RV (ConLeche.nativeRulesOk recCP rlvlsP pw nP n csP
        (kinds.map (·.map kindOf)) rhssP recTyP)) := by
  sorry

/-! ## The recogniser -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:501-523 nativeCounts?
— con-leche's `match` on the WHOLE pair re-read as a match on its second
component, which is what the arena's `view` dispatch decides. -/
theorem nativeCounts_eq (nPd : Nat) (cvTP : ConstantVal)
    (csP : List (ConstantVal × Nat × Nat)) (mI rP : Nat) :
    ConLeche.nativeCounts? nPd cvTP csP mI rP =
      (match (cvTP.type.piBinders).2 with
       | .sort _ =>
         if nPd ≤ (cvTP.type.piBinders).1.length then
           some (nPd, (cvTP.type.piBinders).1.length - nPd) else none
       | _ =>
         if rP < csP.length + 1 || mI < rP then none
         else if rP - (csP.length + 1) == nPd then some (nPd, mI - rP) else none) := by
  simp only [ConLeche.nativeCounts?]
  cases h : cvTP.type.piBinders with
  | mk bs body => cases body <;> simp [h]

/-- con-leche: none — `nativeCounts?`'s NON-sort tail, both sides: the
recursor's claimed prefix against the constructor count.  Stated separately so
the nine non-`sort` arms of the `view` dispatch close with one
`all_goals`. -/
theorem nativeCounts_tail {nPd : Nat} {cvTP : ConstantVal}
    {csP : List (ConstantVal × Nat × Nat)} {mI rP : Nat}
    {cs : List (IConstantVal × Nat × Nat)} {s s' : AState}
    {r : Option (Nat × Nat)} (hcsl : cs.length = csP.length)
    (hns : ∀ l, (cvTP.type.piBinders).2 ≠ .sort l)
    (hz : (if rP < cs.length + 1 || mI < rP then (pure none : AM (Option (Nat × Nat)))
           else if rP - (cs.length + 1) == nPd then pure (some (nPd, mI - rP))
           else pure none) s = .ok (r, s')) :
    s' = s ∧ r = ConLeche.nativeCounts? nPd cvTP csP mI rP := by
  rw [nativeCounts_eq]
  have hm : (match (cvTP.type.piBinders).2 with
      | .sort _ =>
        if nPd ≤ (cvTP.type.piBinders).1.length then
          some (nPd, (cvTP.type.piBinders).1.length - nPd) else none
      | _ =>
        if rP < csP.length + 1 || mI < rP then none
        else if rP - (csP.length + 1) == nPd then some (nPd, mI - rP) else none)
      = (if rP < csP.length + 1 || mI < rP then none
         else if rP - (csP.length + 1) == nPd then some (nPd, mI - rP) else none) := by
    cases hb : (cvTP.type.piBinders).2
    case sort l => exact absurd hb (hns l)
    all_goals rfl
  rw [hm, ← hcsl]
  split at hz
  · obtain ⟨rfl, rfl⟩ := pureOk hz
    exact ⟨rfl, by rw [if_pos ‹_›]⟩
  · rw [if_neg ‹_›]
    split at hz
    · obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨rfl, by rw [if_pos ‹_›]⟩
    · obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨rfl, by rw [if_neg ‹_›]⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:501-523 nativeCounts?
The declared parameter and index counts, or `none`.

**CLOSED** (task #97-P3-Ind round 5): `piBinders_spec` (closed in round 2),
the ten-way `view` dispatch at its residual, `denoteBinders_length` for the
telescope's length and `denoteCtors3_length` for the constructor count.  Round
1's note said `piSortTeleLen?`; the twin reads `piBinders`, whose spec was
already in this file. -/
theorem nativeCounts?_spec (nPd : Nat) (cvT : IConstantVal)
    (cvTP : ConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (csP : List (ConstantVal × Nat × Nat)) (mI rP : Nat) :
    PSpec (fun st => Frontend.denoteCV st cvT = some cvTP ∧
        denoteCtors3 st cs = some csP)
      (Arena.nativeCounts? nPd cvT cs mI rP)
      (RV (ConLeche.nativeCounts? nPd cvTP csP mI rP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hcv, hcs⟩ := hpre
  simp only [Arena.nativeCounts?] at hrun
  obtain ⟨q, s1, k1, hz1⟩ := bindOk hrun
  obtain ⟨p1, hbs, hbody⟩ :=
    piBinders_spec Arena.coreWalkFuel cvT.type cvTP.type s₀ s1 q hok
      (denoteCV_type hcv) k1
  obtain ⟨v, s2, k2, hz2⟩ := bindOk hz1
  obtain ⟨hs2, hview⟩ := view_run k2
  rw [hs2] at hz2
  have hlen : q.1.length = (cvTP.type.piBinders).1.length :=
    denoteBinders_length hbs
  have hcsl : cs.length = csP.length := denoteCtors3_length hcs
  have hbv : denoteEView s1.store v = some (cvTP.type.piBinders).2 := by
    rw [← denoteE_view_eq p1.ok.wf hview]; exact hbody
  cases v
  case sort u =>
    obtain ⟨l, hEq, _⟩ := denote_sort_inv p1.ok.wf hview hbody
    obtain ⟨rfl, rfl⟩ := pureOk hz2
    refine ⟨p1, ?_⟩
    show _ = ConLeche.nativeCounts? nPd cvTP csP mI rP
    rw [nativeCounts_eq, hEq, hlen]
  all_goals
    (obtain ⟨rfl, hr⟩ := nativeCounts_tail hcsl
       (ExprOps.denoteEView_not_sort hbv (by simp)) hz2
     exact ⟨p1, hr⟩)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:525-549 nativeRecPinOk
The stream's recursor record passed the structural pin.  Pure on both sides.

**CLOSED** (task #97-P3-Ind round 5), at round 4's corrected statement — see
`nativeRecLpsOk_spec` below for the `StoreWF` hypothesis both gained and why.
The block's `denoteCIList` inverted at the head (`denoteCI_not_ind` closes the
six kinds that are not the type former), `sumSplit_spec` for the members after
it, `denoteCtors_length`/`denoteRules_length` for the two counts, and — at
each position of the rule/constructor zip — `denoteRules_getElem?` and
`denoteCtors3_getElem?` with `beq_handle_eq` at the constructor name. -/
theorem nativeRecPinOk_spec (st : EStore) (hwf : StoreWF st)
    (p : Arena.InductiveShape) (q : ConLeche.InductiveShape)
    (block : List IConstantInfo) (blockP : List ConstantInfo)
    (hp : ShapeRel st p q)
    (hb : Frontend.denoteCIList st block = some blockP) :
    Arena.nativeRecPinOk p block = ConLeche.nativeRecPinOk q blockP := by
  have hctl : p.ctors.length = q.ctors.length := denoteCtors_length _ _ hp.ctors
  cases block with
  | nil =>
    simp only [Frontend.denoteCIList, Option.some.injEq] at hb
    subst hb; rfl
  | cons c rest =>
    simp only [Frontend.denoteCIList] at hb
    cases hc : Frontend.denoteCI st c with
    | none => rw [hc] at hb; simp at hb
    | some cP =>
      cases hr : Frontend.denoteCIList st rest with
      | none => rw [hc, hr] at hb; simp at hb
      | some restP =>
        rw [hc, hr] at hb
        obtain rfl := Option.some.inj hb
        cases c
        case indInfo v caps =>
          simp only [Frontend.denoteCI] at hc
          cases hcv : Frontend.denoteCV st v with
          | none => rw [hcv] at hc; simp at hc
          | some vP =>
            cases hcp : Frontend.denoteCaps st caps with
            | none => rw [hcv, hcp] at hc; simp at hc
            | some capsP =>
              rw [hcv, hcp] at hc
              obtain rfl := Option.some.inj hc
              have hsp := sumSplit_spec st rest restP hr
              simp only [Arena.nativeRecPinOk, ConLeche.nativeRecPinOk]
              cases hA : Arena.sumSplit rest with
              | none =>
                rw [hA] at hsp
                simp only [ROp] at hsp
                rw [hsp]
              | some a =>
                rw [hA] at hsp
                simp only [ROp] at hsp
                obtain ⟨b, hbq, hrel⟩ := hsp
                rw [hbq]
                obtain ⟨cs, cvR, mI, rP, rules⟩ := a
                obtain ⟨csP, cvRP, mIP, rPP, rulesP⟩ := b
                have hcts : denoteCtors3 st cs = some csP := hrel.ctors
                have hrls : Frontend.denoteRules st rules = some rulesP :=
                  hrel.rules
                have hmI : mI = mIP := hrel.mI
                have hrP : rP = rPP := hrel.rP
                simp only [hmI, hrP, hp.nP, hp.nIdx, hctl,
                  denoteRules_length hrls]
                congr 1
                congr 1
                funext j
                obtain ⟨hrA, hrB⟩ := denoteRules_getElem? hrls j
                obtain ⟨hcA, hcB⟩ := denoteCtors3_getElem? hcts j
                cases hj : rules[j]? with
                | none => rw [hrB hj]
                | some rule =>
                  obtain ⟨x, hx, hd⟩ := hrA rule hj
                  rw [hx]
                  cases hk : cs[j]? with
                  | none => rw [hcB hk]
                  | some e =>
                    obtain ⟨cvC, aa, bb⟩ := e
                    obtain ⟨c', hc', hdcv⟩ := hcA cvC aa bb hk
                    rw [hc']
                    obtain ⟨hct, hnf⟩ := denoteRule_ctor hd
                    simp only [beq_handle_eq hwf hct (denoteCV_name hdcv), hnf]
        all_goals
          (have hne := denoteCI_not_ind hc (by simp)
           cases cP
           case indInfo aa bb => exact absurd rfl (hne aa bb)
           all_goals rfl)

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:551-560 nativeRecLpsOk
The recursor's level parameters are the block's (with the elimination
parameter in front at the large eliminator).  Pure on both sides.

**PROVED** (round 4), at the corrected statement — see `nativeRecPinOk_spec`
above for the hypothesis this gained and why.  `beq_nhandleList_eq`
(`Bridge/Inductives/Rel.lean`, new: `denoteEList_inj`'s twin at NAME handles)
is the whole proof, at the two level-parameter lists and at the eliminator
handle consed in front of one of them. -/
theorem nativeRecLpsOk_spec (st : EStore) (hwf : StoreWF st)
    (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (hp : ShapeRel st p q) :
    Arena.nativeRecLpsOk p = ConLeche.nativeRecLpsOk q := by
  have hlpsR : Frontend.denoteNList st.ns p.cvR.levelParams
      = some q.cvR.levelParams := denoteCV_lps hp.cvR
  have hlpsT : Frontend.denoteNList st.ns p.cvT.levelParams
      = some q.cvT.levelParams := denoteCV_lps hp.cvT
  have hcons : Frontend.denoteNList st.ns (p.elim :: p.cvT.levelParams)
      = some (q.elim :: q.cvT.levelParams) := by
    simp only [Frontend.denoteNList, hp.elim, hlpsT]
  simp only [Arena.nativeRecLpsOk, ConLeche.nativeRecLpsOk, hp.large]
  cases q.large with
  | true => simpa using beq_nhandleList_eq hwf hlpsR hcons
  | false => simpa using beq_nhandleList_eq hwf hlpsR hlpsT

/-! ### The recogniser's dispatch (task #97-P3-Ind round 6)

`StructParts.lean`'s `structPartsCore?_run` shape: one inversion at `PStep`
under `StateOK` + `PinsOK`, the record carried under a `CheckOK` hypothesis at
the initial state (only `isProp` — `lvlEq?`'s verdict — needs it), feeding
`nativeShape?_spec`, `nativeParts?_spec`'s shape half and `nativeParts?_isSome`. -/

/-- con-leche: none — `sumSplit`'s constructor list survives an append. -/
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

/-- con-leche: none — the shape record's constructor list, read off
`sumSplit`'s. -/
theorem denoteCtors3_map {st : EStore} :
    ∀ (cs : List (IConstantVal × Nat × Nat)) (csP : List (ConstantVal × Nat × Nat)),
      denoteCtors3 st cs = some csP →
      denoteCtors st (cs.map fun c => (c.1, c.2.2)) =
        some (csP.map fun c => (c.1, c.2.2)) := by
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
        simp only [List.map_cons, denoteCtors, h1, ih xs h2]

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

/-- con-leche: none — the recogniser's per-constructor guard is a name-level
guard. -/
theorem ctors_all_eq {st : EStore} (hwf : StoreWF st) (nP : Nat)
    {lps : List NIdx} {lpsP : List ConLeche.Name} {res : List NIdx}
    {resP : List ConLeche.Name}
    (hlps : Frontend.denoteNList st.ns lps = some lpsP)
    (hres : Frontend.denoteNList st.ns res = some resP) :
    ∀ (cs : List (IConstantVal × Nat × Nat)) (csP : List (ConstantVal × Nat × Nat)),
      denoteCtors3 st cs = some csP →
      (cs.all fun c => c.2.1 == nP && c.1.levelParams == lps &&
          res.contains c.1.name == false) =
        (csP.all fun c => c.2.1 == nP && c.1.levelParams == lpsP &&
          resP.contains c.1.name == false) := by
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
        simp only [List.all_cons, ih xs h2,
          beq_nhandleList_eq hwf (denoteCV_lps h1) hlps,
          denoteNList_contains hwf _ _ hres _ _ (denoteCV_name h1)]

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
— **the recogniser's run, inverted once**. -/
theorem nativeShape?_run (nPd : Nat) (block : List IConstantInfo)
    (blockP : List ConstantInfo) (s₀ s' : AState) (r : Option Arena.InductiveShape)
    (hok : StateOK s₀) (hpin : PinsOK s₀)
    (hb : Frontend.denoteCIList s₀.store block = some blockP)
    (hrun : Arena.nativeShape? nPd block s₀ = .ok (r, s')) :
    PStep s₀ s' ∧
      ROp (fun q st p => ∀ (μ : CheckMode) (env : Env) (fe : IFEnv),
          CheckOK μ env fe s₀ → ShapeRel st p q)
        (ConLeche.nativeShape? nPd blockP) s'.store r := by
  unfold Arena.nativeShape? at hrun
  split at hrun
  case h_2 hne =>
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show ConLeche.nativeShape? nPd blockP = none
    unfold ConLeche.nativeShape?
    split
    · rename_i cvTP capsP rest
      rcases block with _ | ⟨c, cs⟩
      · simp [Frontend.denoteCIList] at hb
      obtain ⟨x, xs, e, hc, -⟩ := denoteCIList_cons_eq hb
      simp only [List.cons.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      obtain ⟨v, caps, rfl⟩ := denoteCI_ind_shape hc
      exact absurd rfl (hne _ _ _)
    · rfl
  rename_i cvT caps rest
  obtain ⟨x, restP, e, hc, hrest⟩ := denoteCIList_cons_eq hb
  subst e
  simp only [Frontend.denoteCI] at hc
  cases hcvT : Frontend.denoteCV s₀.store cvT with
  | none => rw [hcvT] at hc; simp at hc
  | some cvTP =>
  cases hcaps : Frontend.denoteCaps s₀.store caps with
  | none => rw [hcvT, hcaps] at hc; simp at hc
  | some capsP =>
  rw [hcvT, hcaps] at hc
  obtain rfl := (Option.some.inj hc).symm
  have hT := denoteCV_name hcvT
  have hlps := denoteCV_lps hcvT
  have hTty := denoteCV_type hcvT
  have hsplit := sumSplit_spec s₀.store rest restP hrest
  cases hsp : Arena.sumSplit rest with
  | none =>
    rw [hsp] at hrun hsplit
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show ConLeche.nativeShape? nPd _ = none
    simp only [ConLeche.nativeShape?, show ConLeche.sumSplit restP = none from hsplit]
  | some q =>
  rw [hsp] at hrun hsplit
  obtain ⟨qP, hqP, hrel⟩ := hsplit
  obtain ⟨cs, cvR, mI, rP, rules⟩ := q
  obtain ⟨csP, cvRP, mIP, rPP, rulesP⟩ := qP
  obtain ⟨hcs, hcvR, hmI, hrP, hrules⟩ := hrel
  simp only at hmI hrP hcs hcvR hrules
  subst hmI hrP
  have hR := denoteCV_name hcvR
  have hRlps := denoteCV_lps hcvR
  dsimp only at hrun
  obtain ⟨cnt, s1, k1, hz1⟩ := bindOk hrun
  obtain ⟨p1, hcnt⟩ := nativeCounts?_spec nPd cvT cvTP cs csP mI rP s₀ s1 cnt hok
    ⟨hcvT, hcs⟩ k1
  have hcnt' : cnt = ConLeche.nativeCounts? nPd cvTP csP mI rP := hcnt
  subst hcnt'
  simp only [ConLeche.nativeShape?, hqP]
  cases hcntP : ConLeche.nativeCounts? nPd cvTP csP mI rP with
  | none =>
    rw [hcntP] at hz1
    obtain ⟨rfl, rfl⟩ := pureOk hz1
    exact ⟨p1, rfl⟩
  | some np =>
  obtain ⟨nP, nIdx⟩ := np
  rw [hcntP] at hz1
  dsimp only
  obtain ⟨reserved, s2, k2, hz2⟩ := bindOk hz1
  obtain ⟨p2, hres⟩ := reservedBasisNames_pstep p1.ok (hpin.mono p1.ext p1.pins) k2
  have q2 : PStep s₀ s2 := p1.trans p2
  have x2 := q2.ext
  rw [denoteNList_contains q2.ok.wf _ _ hres _ _ (denoteN_ext hT x2),
    denoteNList_contains q2.ok.wf _ _ hres _ _ (denoteN_ext hR x2),
    ctors_all_eq q2.ok.wf nP (denoteNListE_ext x2 _ _ hlps) hres cs csP
      (denoteCtors3_ext x2 _ _ hcs)] at hz2
  split at hz2
  case isFalse hc =>
    obtain ⟨rfl, rfl⟩ := pureOk hz2
    refine ⟨q2, ?_⟩
    show _ = none
    rw [if_neg hc]
  case isTrue hc =>
  rw [if_pos hc]
  generalize hsP : ConLeche.nativeShape?.match_1 (fun _ => Level)
    (Expr.stripPis (nP + nIdx) cvTP.type) (fun _ s => s) (fun _ => Level.zero) = sP
  obtain ⟨tq, s6, k6, hz6⟩ := bindOk hz2
  obtain ⟨hs6, htq⟩ := stripPis_pstep q2.ok (denote_ext hTty q2.ext) k6
  rw [hs6] at hz6
  rcases tq with _ | ⟨tbs, tbody⟩
  · have e : sP = .zero := by rw [← hsP, stripPis_none htq]
    obtain ⟨y, s7, k7, hz7⟩ := bindOk hz6
    obtain ⟨hs7, hy⟩ := zeroLevel_run (hpin.mono q2.ext q2.pins) k7
    have q7 : PStep s₀ s7 := by rw [hs7]; exact q2
    have hy7 : denoteL s7.store.ls y = some sP := by rw [hs7, e]; exact hy
    obtain ⟨z, s8, k8, hz8⟩ := bindOk hz7
    obtain ⟨hs8, hzl⟩ := zeroLevel_run (hpin.mono q7.ext q7.pins) k8
    rw [hs8] at hz8
    obtain ⟨v, s9, k9, hz9⟩ := bindOk hz8
    have p9 := lvlEq?_pstep q7.ok k9
    have q9 : PStep s₀ s9 := q7.trans p9
    have hprop : ∀ (μ : CheckMode) (env : Env) (fe : IFEnv), CheckOK μ env fe s₀ →
        v = Level.isEquiv sP .zero := by
      intro μ env fe hc
      have hcY := (q7.toCore hc).ok
      obtain ⟨-, -, -, lu, lv, hlu, hlv, ha⟩ :=
        AM.of_run (P := fun t => t = s7) rfl k9 (Core.lvlEq?_spec s7 y z hcY)
      rw [hy7] at hlu; rw [hzl] at hlv
      cases hlu; cases hlv; exact ha
    have hY9 : denoteL s9.store.ls y = some sP := denoteL_ext hy7 p9.ext
    have hctors := denoteCtors_ext q9.ext _ _ (denoteCtors3_map cs csP hcs)
    have hrhss := denoteEList_ext q9.ext _ _ (denoteRules_rhss rules rulesP hrules)
    cases hlp : cvR.levelParams with
    | nil =>
      have hlpP : cvRP.levelParams = [] := by
        rw [hlp] at hRlps; simp [Frontend.denoteNList] at hRlps; exact hRlps
      rw [hlp] at hz9
      simp only [hlpP]
      obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz9
      obtain ⟨pA, hanon⟩ := internNNode_run q9.ok
        (by intro c hc; simp [NNodeView.children] at hc) kA
      have xA : Ext s₀.store sA.store := q9.ext.trans pA.ext
      obtain ⟨rfl, rfl⟩ := pureOk hzA
      refine ⟨q9.trans pA, _, rfl, fun μ env fe hc => ?_⟩
      exact { cvT := denoteCV_ext hcvT xA, ctors := denoteCtors_ext pA.ext _ _ hctors,
              nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR xA,
              elim := by rw [hanon]; rfl, resSort := denoteL_ext hY9 pA.ext,
              rhss := denoteEList_ext pA.ext _ _ hrhss, large := rfl,
              isProp := by rw [hprop μ env fe hc] }
    | cons elim relps =>
      rw [hlp] at hRlps
      simp only [Frontend.denoteNList] at hRlps
      cases helim : denoteN s₀.store.ns elim with
      | none => rw [helim] at hRlps; simp at hRlps
      | some elimP =>
      cases hrel : Frontend.denoteNList s₀.store.ns relps with
      | none => rw [helim, hrel] at hRlps; simp at hRlps
      | some relpsP =>
      rw [helim, hrel] at hRlps
      have hlpP : cvRP.levelParams = elimP :: relpsP := (Option.some.inj hRlps).symm
      have g8 : (relps == cvT.levelParams) = (relpsP == cvTP.levelParams) :=
        beq_nhandleList_eq q9.ok.wf (denoteNListE_ext q9.ext _ _ hrel)
          (denoteNListE_ext q9.ext _ _ hlps)
      have g9 : cvT.levelParams.contains elim = cvTP.levelParams.contains elimP :=
        denoteNList_contains q9.ok.wf _ _ (denoteNListE_ext q9.ext _ _ hlps) _ _
          (denoteN_ext helim q9.ext)
      rw [hlp] at hz9
      dsimp only at hz9
      simp only [hlpP]
      rw [g8, g9] at hz9
      by_cases hc2 : (relpsP == cvTP.levelParams && !cvTP.levelParams.contains elimP) = true
      · rw [if_pos hc2] at hz9 ⊢
        obtain ⟨rfl, rfl⟩ := pureOk hz9
        refine ⟨q9, _, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT q9.ext, ctors := hctors,
                nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR q9.ext,
                elim := denoteN_ext helim q9.ext, resSort := hY9,
                rhss := hrhss, large := rfl,
                isProp := by rw [hprop μ env fe hc] }
      · rw [if_neg hc2] at hz9 ⊢
        obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz9
        obtain ⟨pA, hanon⟩ := internNNode_run q9.ok
          (by intro c hc; simp [NNodeView.children] at hc) kA
        have xA : Ext s₀.store sA.store := q9.ext.trans pA.ext
        obtain ⟨rfl, rfl⟩ := pureOk hzA
        refine ⟨q9.trans pA, _, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT xA, ctors := denoteCtors_ext pA.ext _ _ hctors,
                nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR xA,
                elim := by rw [hanon]; rfl, resSort := denoteL_ext hY9 pA.ext,
                rhss := denoteEList_ext pA.ext _ _ hrhss, large := rfl,
                isProp := by rw [hprop μ env fe hc] }

  obtain ⟨txs, tbodyP, hspt, -, htbody⟩ := denoteBP_someB htq
  obtain ⟨tv, s7, k7, hz7⟩ := bindOk hz6
  obtain ⟨hs7, htv⟩ := view_run k7
  rw [hs7] at hz7
  have htbv : denoteEView s2.store tv = some tbodyP := by
    rw [← denoteE_view_eq q2.ok.wf htv]; exact htbody
  split at hz7
  case h_1 u =>
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv q2.ok.wf htv htbody
    have e : sP = l := by rw [← hsP, hspt]
    obtain ⟨y, sy, ky, hz8⟩ := bindOk hz7
    obtain ⟨hyu, hsy⟩ := pureOk ky
    rw [hsy] at hz8
    have hyl : denoteL s2.store.ls y = some sP := by rw [hyu, e]; exact hl
    obtain ⟨z, s8, k8, hz8⟩ := bindOk hz8
    obtain ⟨hs8, hzl⟩ := zeroLevel_run (hpin.mono q2.ext q2.pins) k8
    rw [hs8] at hz8
    obtain ⟨v, s9, k9, hz9⟩ := bindOk hz8
    have p9 := lvlEq?_pstep q2.ok k9
    have q9 : PStep s₀ s9 := q2.trans p9
    have hprop : ∀ (μ : CheckMode) (env : Env) (fe : IFEnv), CheckOK μ env fe s₀ →
        v = Level.isEquiv sP .zero := by
      intro μ env fe hc
      have hcY := (q2.toCore hc).ok
      obtain ⟨-, -, -, lu, lv, hlu, hlv, ha⟩ :=
        AM.of_run (P := fun t => t = s2) rfl k9 (Core.lvlEq?_spec s2 y z hcY)
      rw [hyl] at hlu; rw [hzl] at hlv
      cases hlu; cases hlv; exact ha
    have hY9 : denoteL s9.store.ls y = some sP := denoteL_ext hyl p9.ext
    have hctors := denoteCtors_ext q9.ext _ _ (denoteCtors3_map cs csP hcs)
    have hrhss := denoteEList_ext q9.ext _ _ (denoteRules_rhss rules rulesP hrules)
    cases hlp : cvR.levelParams with
    | nil =>
      have hlpP : cvRP.levelParams = [] := by
        rw [hlp] at hRlps; simp [Frontend.denoteNList] at hRlps; exact hRlps
      rw [hlp] at hz9
      simp only [hlpP]
      obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz9
      obtain ⟨pA, hanon⟩ := internNNode_run q9.ok
        (by intro c hc; simp [NNodeView.children] at hc) kA
      have xA : Ext s₀.store sA.store := q9.ext.trans pA.ext
      obtain ⟨rfl, rfl⟩ := pureOk hzA
      refine ⟨q9.trans pA, _, rfl, fun μ env fe hc => ?_⟩
      exact { cvT := denoteCV_ext hcvT xA, ctors := denoteCtors_ext pA.ext _ _ hctors,
              nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR xA,
              elim := by rw [hanon]; rfl, resSort := denoteL_ext hY9 pA.ext,
              rhss := denoteEList_ext pA.ext _ _ hrhss, large := rfl,
              isProp := by rw [hprop μ env fe hc] }
    | cons elim relps =>
      rw [hlp] at hRlps
      simp only [Frontend.denoteNList] at hRlps
      cases helim : denoteN s₀.store.ns elim with
      | none => rw [helim] at hRlps; simp at hRlps
      | some elimP =>
      cases hrel : Frontend.denoteNList s₀.store.ns relps with
      | none => rw [helim, hrel] at hRlps; simp at hRlps
      | some relpsP =>
      rw [helim, hrel] at hRlps
      have hlpP : cvRP.levelParams = elimP :: relpsP := (Option.some.inj hRlps).symm
      have g8 : (relps == cvT.levelParams) = (relpsP == cvTP.levelParams) :=
        beq_nhandleList_eq q9.ok.wf (denoteNListE_ext q9.ext _ _ hrel)
          (denoteNListE_ext q9.ext _ _ hlps)
      have g9 : cvT.levelParams.contains elim = cvTP.levelParams.contains elimP :=
        denoteNList_contains q9.ok.wf _ _ (denoteNListE_ext q9.ext _ _ hlps) _ _
          (denoteN_ext helim q9.ext)
      rw [hlp] at hz9
      dsimp only at hz9
      simp only [hlpP]
      rw [g8, g9] at hz9
      by_cases hc2 : (relpsP == cvTP.levelParams && !cvTP.levelParams.contains elimP) = true
      · rw [if_pos hc2] at hz9 ⊢
        obtain ⟨rfl, rfl⟩ := pureOk hz9
        refine ⟨q9, _, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT q9.ext, ctors := hctors,
                nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR q9.ext,
                elim := denoteN_ext helim q9.ext, resSort := hY9,
                rhss := hrhss, large := rfl,
                isProp := by rw [hprop μ env fe hc] }
      · rw [if_neg hc2] at hz9 ⊢
        obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz9
        obtain ⟨pA, hanon⟩ := internNNode_run q9.ok
          (by intro c hc; simp [NNodeView.children] at hc) kA
        have xA : Ext s₀.store sA.store := q9.ext.trans pA.ext
        obtain ⟨rfl, rfl⟩ := pureOk hzA
        refine ⟨q9.trans pA, _, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT xA, ctors := denoteCtors_ext pA.ext _ _ hctors,
                nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR xA,
                elim := by rw [hanon]; rfl, resSort := denoteL_ext hY9 pA.ext,
                rhss := denoteEList_ext pA.ext _ _ hrhss, large := rfl,
                isProp := by rw [hprop μ env fe hc] }

  case h_2 hne =>
    have hns := ExprOps.denoteEView_not_sort htbv hne
    have e : sP = .zero := by
      rw [← hsP, hspt]
      cases tbodyP <;> first | rfl | exact absurd rfl (hns _)
    obtain ⟨y, sy, ky, hz8⟩ := bindOk hz7
    obtain ⟨hsy, hy⟩ := zeroLevel_run (hpin.mono q2.ext q2.pins) ky
    have qy : PStep s₀ sy := by rw [hsy]; exact q2
    have hyy : denoteL sy.store.ls y = some sP := by rw [hsy, e]; exact hy
    obtain ⟨z, s8, k8, hz8⟩ := bindOk hz8
    obtain ⟨hs8, hzl⟩ := zeroLevel_run (hpin.mono qy.ext qy.pins) k8
    rw [hs8] at hz8
    obtain ⟨v, s9, k9, hz9⟩ := bindOk hz8
    have p9 := lvlEq?_pstep qy.ok k9
    have q9 : PStep s₀ s9 := qy.trans p9
    have hprop : ∀ (μ : CheckMode) (env : Env) (fe : IFEnv), CheckOK μ env fe s₀ →
        v = Level.isEquiv sP .zero := by
      intro μ env fe hc
      have hcY := (qy.toCore hc).ok
      obtain ⟨-, -, -, lu, lv, hlu, hlv, ha⟩ :=
        AM.of_run (P := fun t => t = sy) rfl k9 (Core.lvlEq?_spec sy y z hcY)
      rw [hyy] at hlu; rw [hzl] at hlv
      cases hlu; cases hlv; exact ha
    have hY9 : denoteL s9.store.ls y = some sP := denoteL_ext hyy p9.ext
    have hctors := denoteCtors_ext q9.ext _ _ (denoteCtors3_map cs csP hcs)
    have hrhss := denoteEList_ext q9.ext _ _ (denoteRules_rhss rules rulesP hrules)
    cases hlp : cvR.levelParams with
    | nil =>
      have hlpP : cvRP.levelParams = [] := by
        rw [hlp] at hRlps; simp [Frontend.denoteNList] at hRlps; exact hRlps
      rw [hlp] at hz9
      simp only [hlpP]
      obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz9
      obtain ⟨pA, hanon⟩ := internNNode_run q9.ok
        (by intro c hc; simp [NNodeView.children] at hc) kA
      have xA : Ext s₀.store sA.store := q9.ext.trans pA.ext
      obtain ⟨rfl, rfl⟩ := pureOk hzA
      refine ⟨q9.trans pA, _, rfl, fun μ env fe hc => ?_⟩
      exact { cvT := denoteCV_ext hcvT xA, ctors := denoteCtors_ext pA.ext _ _ hctors,
              nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR xA,
              elim := by rw [hanon]; rfl, resSort := denoteL_ext hY9 pA.ext,
              rhss := denoteEList_ext pA.ext _ _ hrhss, large := rfl,
              isProp := by rw [hprop μ env fe hc] }
    | cons elim relps =>
      rw [hlp] at hRlps
      simp only [Frontend.denoteNList] at hRlps
      cases helim : denoteN s₀.store.ns elim with
      | none => rw [helim] at hRlps; simp at hRlps
      | some elimP =>
      cases hrel : Frontend.denoteNList s₀.store.ns relps with
      | none => rw [helim, hrel] at hRlps; simp at hRlps
      | some relpsP =>
      rw [helim, hrel] at hRlps
      have hlpP : cvRP.levelParams = elimP :: relpsP := (Option.some.inj hRlps).symm
      have g8 : (relps == cvT.levelParams) = (relpsP == cvTP.levelParams) :=
        beq_nhandleList_eq q9.ok.wf (denoteNListE_ext q9.ext _ _ hrel)
          (denoteNListE_ext q9.ext _ _ hlps)
      have g9 : cvT.levelParams.contains elim = cvTP.levelParams.contains elimP :=
        denoteNList_contains q9.ok.wf _ _ (denoteNListE_ext q9.ext _ _ hlps) _ _
          (denoteN_ext helim q9.ext)
      rw [hlp] at hz9
      dsimp only at hz9
      simp only [hlpP]
      rw [g8, g9] at hz9
      by_cases hc2 : (relpsP == cvTP.levelParams && !cvTP.levelParams.contains elimP) = true
      · rw [if_pos hc2] at hz9 ⊢
        obtain ⟨rfl, rfl⟩ := pureOk hz9
        refine ⟨q9, _, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT q9.ext, ctors := hctors,
                nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR q9.ext,
                elim := denoteN_ext helim q9.ext, resSort := hY9,
                rhss := hrhss, large := rfl,
                isProp := by rw [hprop μ env fe hc] }
      · rw [if_neg hc2] at hz9 ⊢
        obtain ⟨anon, sA, kA, hzA⟩ := bindOk hz9
        obtain ⟨pA, hanon⟩ := internNNode_run q9.ok
          (by intro c hc; simp [NNodeView.children] at hc) kA
        have xA : Ext s₀.store sA.store := q9.ext.trans pA.ext
        obtain ⟨rfl, rfl⟩ := pureOk hzA
        refine ⟨q9.trans pA, _, rfl, fun μ env fe hc => ?_⟩
        exact { cvT := denoteCV_ext hcvT xA, ctors := denoteCtors_ext pA.ext _ _ hctors,
                nP := rfl, nIdx := rfl, cvR := denoteCV_ext hcvR xA,
                elim := by rw [hanon]; rfl, resSort := denoteL_ext hY9 pA.ext,
                rhss := denoteEList_ext pA.ext _ _ hrhss, large := rfl,
                isProp := by rw [hprop μ env fe hc] }


/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
Read a block into the shape record, or refuse it.  **Two-sided**: the dispatch
reads it.

**CORE grade, not pure** (task #97-P3-Ind round 2's finding; the argument is
in `Bridge/Inductives/Rel.lean`'s frame section).  Like `structPartsCore?`
this recogniser asks `lvlEq? s z` for `isProp`.  Task #97-P3-Frame made the
FRAME provable at `StateOK` and left the grade alone: `RShape` carries
`ShapeRel.isProp`, so the ANSWER still needs `LvlEqCacheOK` and `StateOK` does
not carry it.

**CLOSED** (task #97-P3-Ind round 6): `nativeShape?_run` at the `CheckOK` it
was handed. -/
theorem nativeShape?_spec {μ : CheckMode} {env : Env} (fe : IFEnv) (nPd : Nat)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.nativeShape? nPd block)
      (ROp RShape (ConLeche.nativeShape? nPd blockP)) := by
  intro s₀ s' r hok hb hrun
  obtain ⟨hstep, hrel⟩ :=
    nativeShape?_run nPd block blockP s₀ s' r hok.state hok.pins hb hrun
  exact ⟨hstep.toCore hok, hrel.mono (fun _ _ h => h μ env fe hok)⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:631-652 nativeParts?
— the shared inversion of `nativeParts?_spec` and `nativeParts?_isSome`:
`nativeShape?_run`, the placeholder kinds, and `nativeRecPinOk_spec` at the
final store. -/
theorem nativeParts?_run (nPd : Nat) (block : List IConstantInfo)
    (blockP : List ConstantInfo) (s₀ s' : AState) (r : Option Arena.NativeParts)
    (hok : StateOK s₀) (hpin : PinsOK s₀)
    (hb : Frontend.denoteCIList s₀.store block = some blockP)
    (hrun : Arena.nativeParts? nPd block s₀ = .ok (r, s')) :
    PStep s₀ s' ∧
      ROp (fun q st p => ∀ (μ : CheckMode) (env : Env) (fe : IFEnv),
          CheckOK μ env fe s₀ → PartsRel st p q)
        (ConLeche.nativeParts? nPd blockP) s'.store r := by
  simp only [Arena.nativeParts?] at hrun
  obtain ⟨o, s1, k1, hz⟩ := bindOk hrun
  obtain ⟨p1, hrel⟩ := nativeShape?_run nPd block blockP s₀ s1 o hok hpin hb k1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk hz
    refine ⟨p1, ?_⟩
    show ConLeche.nativeParts? nPd blockP = none
    simp only [ConLeche.nativeParts?,
      show ConLeche.nativeShape? nPd blockP = none from hrel, Option.map_none]
  | some p =>
    obtain ⟨q, hq, hpq⟩ := hrel
    obtain ⟨rfl, rfl⟩ := pureOk hz
    refine ⟨p1, _, by rw [ConLeche.nativeParts?, hq]; rfl, ?_⟩
    intro μ env fe hc
    have hs := hpq μ env fe hc
    exact ⟨hs, rfl, nativeRecPinOk_spec _ p1.ok.wf p q block blockP hs
      (denoteCIList_ext p1.ext _ _ hb)⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:631-652 nativeParts?
**THE DISPATCH'S RECOGNISER** — `checkIndDecl` routes on this and on nothing
else (task #219), so its two-sidedness is the soundness of the route choice.

**CORE grade, not pure**, because `nativeShape?` is (task #97-P3-Ind round 2's
finding).  This is the statement `checkIndDecl_bridge` consumes, so round 1's
`PSpec` form was a false lemma UNDER A PROVED THEOREM — the one place in the
tier where the defect was load-bearing rather than merely stated.  Task
#97-P3-Frame left it at `CSpec` for the reason `nativeShape?_spec` gives: the
answer, not the frame, is what needs the cache invariant.

**CLOSED** (task #97-P3-Ind round 6): `nativeParts?_run`.  The kinds are the
placeholder `[]` on both sides (task #210 Part D: the install fills them), so
`recCtorKinds` is not on this statement's path at all. -/
theorem nativeParts?_spec {μ : CheckMode} {env : Env} (fe : IFEnv) (nPd : Nat)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.nativeParts? nPd block)
      (ROp RParts (ConLeche.nativeParts? nPd blockP)) := by
  intro s₀ s' r hok hb hrun
  obtain ⟨hstep, hrel⟩ :=
    nativeParts?_run nPd block blockP s₀ s' r hok.state hok.pins hb hrun
  exact ⟨hstep.toCore hok, hrel.mono (fun _ _ h => h μ env fe hok)⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean nativeParts? —
**the recogniser's `isSome` half at the PURE grade**, the companion of
`StructParts.lean`'s `structPartsCore?_isSome` and the second half of what
`Bridge/Frontend/ProjRec.lean`'s `projRecOwners_run` asks of this tier (task
#97-P3-Frontend's sorry list, item 13).  `projRecOwners` reads both
recognisers through `.isSome` alone and its hypothesis is `StateOK`, so it
cannot consume `nativeParts?_spec`'s `CSpec` — whose `RParts` carries
`ShapeRel.isProp`, which is `lvlEq?`'s verdict.

**`PSpecP`, not `PSpec`**: `nativeShape?` reads `zeroLevel` off the pin table
(`Arena/Inductives/NativeParts.lean:502-504`) and the recogniser tests pinned
names, so `PinsOK` is the licence — task #97-P3-Ind round 3's finding at
`structProjGuards_spec`, applied here.

**CLOSED** (task #97-P3-Ind round 6): `nativeParts?_run` through
`ROp.isSome`. -/
theorem nativeParts?_isSome (nPd : Nat) (block : List IConstantInfo)
    (blockP : List ConstantInfo) :
    PSpecP (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.nativeParts? nPd block)
      (fun _ r => r.isSome = (ConLeche.nativeParts? nPd blockP).isSome) := by
  intro s₀ s' r hok hpin hb hrun
  obtain ⟨hstep, hrel⟩ := nativeParts?_run nPd block blockP s₀ s' r hok hpin hb hrun
  exact ⟨hstep, hrel.isSome⟩

end ConRon.Bridge.Inductives
