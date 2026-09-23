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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, he⟩ := hpre
  simp only [Arena.recFamOk] at hrun
  obtain ⟨us, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hus⟩ := paramLevels_spec lps lpsP s₀ s1 us hok hlps k1
  obtain ⟨hd, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hhd⟩ := internConstE_run p1.ok (denoteN_ext hT p1.ext) hus k2
  have q2 : PStep s₀ s2 := p1.trans p2
  obtain ⟨fn, s3, k3, z3⟩ := bindOk z2
  obtain ⟨hs3, hfn⟩ := getAppFn_run q2.ok (denote_ext he q2.ext) k3
  rw [hs3] at z3
  obtain ⟨args, s4, k4, z4⟩ := bindOk z3
  obtain ⟨hs4, hargs⟩ := getAppArgs_run q2.ok (denote_ext he q2.ext) k4
  rw [hs4] at z4
  obtain ⟨ps, s5, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hps⟩ := structPsAt_spec o nP s2 s5 ps q2.ok trivial k5
  have q5 : PStep s₀ s5 := q2.trans p5
  have e1 := beq_ehandle_eq p5.ok.wf (denote_ext hfn p5.ext) (denote_ext hhd p5.ext)
  have e2 : args.length = eP.getAppArgs.length := (denoteEList_len hargs).symm
  have e3 := beq_ehandleList_eq p5.ok.wf
    (denoteEList_take (denoteEList_ext p5.ext _ _ hargs) nP) hps
  rw [e1, e2, e3] at z5
  split at z5
  case isTrue hc =>
    obtain ⟨rfl, rfl⟩ := pureOk z5
    refine ⟨q5, ?_⟩
    show false = ConLeche.recFamOk TP lpsP nP nIdx o eP
    simp only [Bool.not_eq_true'] at hc
    simp only [ConLeche.recFamOk, hc, Bool.false_and]
  case isFalse hc =>
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
    obtain ⟨p6, hr⟩ := allM_E_pstep (F := fun a => !a.mentionsConst TP)
      (fun st => denoteN st.ns T = some TP) (fun hx h => denoteN_ext h hx)
      (by
        intro a aP t0 t1 b hok0 hq ha hrun0
        obtain ⟨m, t2, q1, w1⟩ := bindOk hrun0
        obtain ⟨o1, hm⟩ := mentionsConst_spec T TP a aP t0 t2 m hok0 ⟨hq, ha⟩ q1
        obtain ⟨rfl, rfl⟩ := pureOk w1
        exact ⟨o1, by rw [hm]⟩)
      _ _ s5 s' r p5.ok (denoteN_ext hT q5.ext)
      (denoteEList_drop (denoteEList_ext p5.ext _ _ hargs) nP) z5
    refine ⟨q5.trans p6, ?_⟩
    show r = ConLeche.recFamOk TP lpsP nP nIdx o eP
    simp only [ConLeche.recFamOk, hc, Bool.true_and, hr]

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:89-111 recPositivity
— **the pure side's leaf clause, selected**: at a term that is not a `∀`,
con-leche's second equation. -/
theorem recPositivity_leaf {TP : ConLeche.Name} {lpsP : List ConLeche.Name}
    {nP nIdx o : Nat} {e : Expr} {k : Nat} (h : ∀ a b c, e ≠ .forallE a b c) :
    ConLeche.recPositivity TP lpsP nP nIdx o e k =
      (if !e.mentionsConst TP then .ordinary
       else if e.getAppFn == Expr.const TP (lpsP.map .param) then
         (if e.getAppArgs.length == nP + nIdx &&
             e.getAppArgs.take nP == ConLeche.structPsAt (o + k) nP then
           (if ConLeche.recFamOk TP lpsP nP nIdx (o + k) e then
             (if k == 0 then .recursive else .reflexive)
            else .negative)
          else .negative)
       else
         match e.getAppFn with
         | .const T' _ => if T' == TP then .negative else .unsupported
         | _ => .unsupported) := by
  cases e
  case forallE a b c => exact absurd rfl (h a b c)
  all_goals (rw [ConLeche.recPositivity] <;> (try rfl) <;> (intro _ _ _ h; cases h))

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
  induction fuel generalizing h hP k with
  | zero =>
    intro s₀ s' r _ _ hrun
    simp only [Arena.recPositivity] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hT, hlps, hh⟩ := hpre
    simp only [Arena.recPositivity] at hrun
    obtain ⟨v, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    have hhv : denoteEView s₀.store v = some hP := by
      rw [← denoteE_view_eq hok.wf hv]; exact hh
    split at z1
    case h_1 dom body m =>
      obtain ⟨domP, bodyP, rfl, hdom, hbody⟩ := denote_forallE_inv hok.wf hv hh
      obtain ⟨mc, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hmc⟩ := mentionsConst_spec T TP dom domP s₀ s2 mc hok ⟨hT, hdom⟩ k2
      have hmc' : mc = domP.mentionsConst TP := hmc
      subst hmc'
      cases hm : domP.mentionsConst TP with
      | true =>
        rw [hm] at z2
        obtain ⟨rfl, rfl⟩ := pureOk z2
        refine ⟨p2, ?_⟩
        show _ = ConLeche.recPositivity TP lpsP nP nIdx o (.forallE domP bodyP m) k
        rw [ConLeche.recPositivity, hm]; rfl
      | false =>
        rw [hm] at z2
        obtain ⟨p3, hr⟩ := ih body bodyP (k + 1) s2 s' r p2.ok
          ⟨denoteN_ext hT p2.ext, denoteNListE_ext p2.ext _ _ hlps, denote_ext hbody p2.ext⟩ z2
        refine ⟨p2.trans p3, ?_⟩
        show _ = ConLeche.recPositivity TP lpsP nP nIdx o (.forallE domP bodyP m) k
        rw [ConLeche.recPositivity, hm]; exact hr
    case h_2 hne =>
      have hns := ExprOps.denoteEView_not_forallE hhv hne
      show PStep s₀ s' ∧ kindOf r = ConLeche.recPositivity TP lpsP nP nIdx o hP k
      rw [recPositivity_leaf hns]
      obtain ⟨mc, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hmc⟩ := mentionsConst_spec T TP h hP s₀ s2 mc hok ⟨hT, hh⟩ k2
      have hmc' : mc = hP.mentionsConst TP := hmc
      subst hmc'
      cases hm : hP.mentionsConst TP with
      | false =>
        rw [hm] at z2
        obtain ⟨rfl, rfl⟩ := pureOk z2
        exact ⟨p2, rfl⟩
      | true =>
      rw [hm] at z2
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      obtain ⟨us, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hus⟩ := paramLevels_spec lps lpsP s2 s3 us p2.ok
        (denoteNListE_ext p2.ext _ _ hlps) k3
      obtain ⟨hd, s4, k4, z4⟩ := bindOk z3
      obtain ⟨p4, hhd⟩ := internConstE_run p3.ok (denoteN_ext hT (p2.ext.trans p3.ext)) hus k4
      have q4 : PStep s₀ s4 := p2.trans (p3.trans p4)
      obtain ⟨fn, s5, k5, z5⟩ := bindOk z4
      obtain ⟨hs5, hfn⟩ := getAppFn_run q4.ok (denote_ext hh q4.ext) k5
      rw [hs5] at z5
      obtain ⟨args, s6, k6, z6⟩ := bindOk z5
      obtain ⟨hs6, hargs⟩ := getAppArgs_run q4.ok (denote_ext hh q4.ext) k6
      rw [hs6] at z6
      have e1 := beq_ehandle_eq q4.ok.wf hfn hhd
      rw [e1] at z6
      split at z6
      case isTrue hc =>
        rw [if_pos hc]
        obtain ⟨ps, s7, k7, z7⟩ := bindOk z6
        obtain ⟨p7, hps⟩ := structPsAt_spec (o + k) nP s4 s7 ps q4.ok trivial k7
        have e2 : args.length = hP.getAppArgs.length := (denoteEList_len hargs).symm
        have e3 := beq_ehandleList_eq p7.ok.wf
          (denoteEList_take (denoteEList_ext p7.ext _ _ hargs) nP) hps
        rw [e2, e3] at z7
        split at z7
        case isTrue hc2 =>
          rw [if_pos hc2]
          obtain ⟨b, s8, k8, z8⟩ := bindOk z7
          obtain ⟨p8, hb⟩ := recFamOk_spec T TP lps lpsP nP nIdx (o + k) h hP s7 s8 b p7.ok
            ⟨denoteN_ext hT (q4.ext.trans p7.ext),
              denoteNListE_ext (q4.ext.trans p7.ext) _ _ hlps,
              denote_ext hh (q4.ext.trans p7.ext)⟩ k8
          have hb' : b = ConLeche.recFamOk TP lpsP nP nIdx (o + k) hP := hb
          subst hb'
          have q8 : PStep s₀ s8 := q4.trans (p7.trans p8)
          cases hfo : ConLeche.recFamOk TP lpsP nP nIdx (o + k) hP with
          | true =>
            rw [hfo] at z8
            obtain ⟨rfl, rfl⟩ := pureOk z8
            refine ⟨q8, ?_⟩
            simp only [if_true]
            cases k <;> rfl
          | false =>
            rw [hfo] at z8
            obtain ⟨rfl, rfl⟩ := pureOk z8
            exact ⟨q8, rfl⟩
        case isFalse hc2 =>
          rw [if_neg hc2]
          obtain ⟨rfl, rfl⟩ := pureOk z7
          exact ⟨q4.trans p7, rfl⟩
      case isFalse hc =>
        rw [if_neg hc]
        obtain ⟨fv, s7, k7, z7⟩ := bindOk z6
        obtain ⟨hs7, hfv⟩ := view_run k7
        rw [hs7] at z7
        split at z7
        case h_1 T' us' =>
          obtain ⟨T'P, lsP, hfe, hT', -⟩ := denote_const_inv q4.ok.wf hfv hfn
          obtain ⟨rfl, rfl⟩ := pureOk z7
          refine ⟨q4, ?_⟩
          rw [hfe]
          dsimp only
          rw [beq_handle_eq q4.ok.wf hT' (denoteN_ext hT q4.ext)]
          cases (T'P == TP) <;> rfl
        case h_2 hnc =>
          have hnc' := denote_not_const q4.ok.wf hfv hfn hnc
          obtain ⟨rfl, rfl⟩ := pureOk z7
          refine ⟨q4, ?_⟩
          split
          · rename_i T' ls hfe; exact absurd hfe (hnc' T' ls)
          · rfl

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:113-116 recFieldKind
The entry at `k = 0`.

`sorry`: `recPositivity_spec`. -/
theorem recFieldKind_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx o : Nat) (dom : EIdx) (domP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st dom = some domP)
      (Arena.recFieldKind T lps nP nIdx o dom)
      (RK (ConLeche.recFieldKind TP lpsP nP nIdx o domP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, hdom⟩ := hpre
  simp only [Arena.recFieldKind] at hrun
  obtain ⟨mc, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hmc⟩ := mentionsConst_spec T TP dom domP s₀ s1 mc hok ⟨hT, hdom⟩ k1
  have hmc' : mc = domP.mentionsConst TP := hmc
  subst hmc'
  cases hm : domP.mentionsConst TP with
  | false =>
    rw [hm] at z1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨p1, ?_⟩
    show _ = ConLeche.recFieldKind TP lpsP nP nIdx o domP
    simp only [ConLeche.recFieldKind, hm]; rfl
  | true =>
    rw [hm] at z1
    obtain ⟨p2, hr⟩ := recPositivity_spec T TP lps lpsP nP nIdx o _ dom domP 0 s1 s' r p1.ok
      ⟨denoteN_ext hT p1.ext, denoteNListE_ext p1.ext _ _ hlps, denote_ext hdom p1.ext⟩ z1
    refine ⟨p1.trans p2, ?_⟩
    show _ = ConLeche.recFieldKind TP lpsP nP nIdx o domP
    simp only [ConLeche.recFieldKind, hm, if_true]; exact hr

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
— the per-field kind con-leche's `let ks` maps, named so that a statement can
mention it (a `match` in a lambda cannot be restated: every restatement is a
new matcher). -/
def recKindAt (TP : ConLeche.Name) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (cty : Expr) (cxs : List (Expr × BinderMeta)) (i : Nat) : ConLeche.RecFieldKind :=
  match ConLeche.recFieldKind TP lpsP nP nIdx i (cxs.getD (nP + i) default).1 with
  | .recursive => if ConLeche.structUsedLater cty nP i then .unsupported else .recursive
  | .reflexive => if ConLeche.structUsedLater cty nP i then .unsupported else .reflexive
  | k => k

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
— the pure side at a peeled telescope, through `recKindAt`. -/
theorem recCtorKinds_some {TP : ConLeche.Name} {lpsP : List ConLeche.Name}
    {nP nIdx : Nat} {cP : ConstantVal × Nat} {cxs : List (Expr × BinderMeta)}
    {cbody : Expr} (h : cP.1.type.stripPis (nP + cP.2) = some (cxs, cbody)) :
    ConLeche.recCtorKinds TP lpsP nP nIdx cP =
      if (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst TP) then
        some ((List.range cP.2).map (recKindAt TP lpsP nP nIdx cP.1.type cxs))
      else some (((List.range cP.2).map (recKindAt TP lpsP nP nIdx cP.1.type cxs)).map
        fun _ => .negative) := by
  simp only [ConLeche.recCtorKinds, h]
  rfl

/-- con-leche: none — `ListRel` at a function of the handle side is a `map`. -/
theorem ListRel.map_eq {β γ : Type} {f : β → γ} {st : EStore} :
    ∀ {bs : List β} {cs : List γ}, ListRel (fun _ b c => f b = c) st bs cs →
      bs.map f = cs := by
  intro bs
  induction bs with
  | nil => intro cs h; cases cs with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons b bs ih =>
    intro cs h
    cases cs with
    | nil => exact h.elim
    | cons c cs =>
      obtain ⟨h1, h2⟩ := h
      simp only [List.map_cons, h1, ih h2]

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, hcv, hc2⟩ := hpre
  have hty := denoteCV_type hcv
  simp only [Arena.recCtorKinds] at hrun
  obtain ⟨q, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hq⟩ := stripPis_pstep hok hty k1
  rw [hs1] at z1
  rcases q with _ | ⟨cbs, cbody⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨PStep.refl hok, ?_⟩
    show _ = none
    simp only [ConLeche.recCtorKinds, ← hc2, stripPis_none hq]
  obtain ⟨cxs, cbodyP, hsp, hcbs, hcb⟩ := denoteBP_someB hq
  have hlenP : cxs.length = nP + c.2 := ConLeche.Expr.stripPis_length _ hsp
  have hlen : cbs.length = nP + c.2 := (denoteBinders_length hcbs).trans hlenP
  have hsp' : cP.1.type.stripPis (nP + cP.2) = some (cxs, cbodyP) := by
    rw [← hc2]; exact hsp
  obtain ⟨ks, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hks⟩ := mapM_pstep (β := Arena.RecFieldKind) (γ := ConLeche.RecFieldKind) _
    (recKindAt TP lpsP nP nIdx cP.1.type cxs) (fun _ b c => kindOf b = c)
    (fun i st => i < c.2 ∧ denoteN st.ns T = some TP ∧
      Frontend.denoteNList st.ns lps = some lpsP ∧
      denoteE st (cbs.getD (nP + i) default).1 = some (cxs.getD (nP + i) default).1 ∧
      denoteE st c.1.type = some cP.1.type)
    (fun _ h => h)
    (fun hx h => ⟨h.1, denoteN_ext h.2.1 hx, denoteNListE_ext hx _ _ h.2.2.1,
      denote_ext h.2.2.2.1 hx, denote_ext h.2.2.2.2 hx⟩)
    (by
      intro i t0 t1 b hok0 hP hrun0
      obtain ⟨hi, hT0, hlps0, hdi, hty0⟩ := hP
      obtain ⟨kk, t2, q1, w1⟩ := bindOk hrun0
      obtain ⟨o1, hk⟩ := recFieldKind_spec T TP lps lpsP nP nIdx i _ _ t0 t2 kk hok0
        ⟨hT0, hlps0, hdi⟩ q1
      have hk' : kindOf kk = ConLeche.recFieldKind TP lpsP nP nIdx i
          (cxs.getD (nP + i) default).1 := hk
      show PStep t0 t1 ∧ kindOf b = recKindAt TP lpsP nP nIdx cP.1.type cxs i
      unfold recKindAt
      rw [← hk']
      cases kk with
      | recursive =>
        obtain ⟨u, t3, q2, w2⟩ := bindOk w1
        obtain ⟨o2, hu⟩ := structUsedLater_spec c.1.type cP.1.type nP i t2 t3 u o1.ok
          (denote_ext hty0 o1.ext) q2
        have hu' : u = ConLeche.structUsedLater cP.1.type nP i := hu
        subst hu'
        obtain ⟨rfl, rfl⟩ := pureOk w2
        refine ⟨o1.trans o2, ?_⟩
        cases ConLeche.structUsedLater cP.1.type nP i <;> rfl
      | reflexive =>
        obtain ⟨u, t3, q2, w2⟩ := bindOk w1
        obtain ⟨o2, hu⟩ := structUsedLater_spec c.1.type cP.1.type nP i t2 t3 u o1.ok
          (denote_ext hty0 o1.ext) q2
        have hu' : u = ConLeche.structUsedLater cP.1.type nP i := hu
        subst hu'
        obtain ⟨rfl, rfl⟩ := pureOk w2
        refine ⟨o1.trans o2, ?_⟩
        cases ConLeche.structUsedLater cP.1.type nP i <;> rfl
      | ordinary => obtain ⟨rfl, rfl⟩ := pureOk w1; exact ⟨o1, rfl⟩
      | negative => obtain ⟨rfl, rfl⟩ := pureOk w1; exact ⟨o1, rfl⟩
      | unsupported => obtain ⟨rfl, rfl⟩ := pureOk w1; exact ⟨o1, rfl⟩)
    (List.range c.2) s₀ s2 ks hok
    (fun i hi => by
      have hi' := List.mem_range.mp hi
      exact ⟨hi', hT, hlps, denoteBinders_getD hcbs (by omega), hty⟩) k2
  have hksm := ListRel.map_eq hks
  obtain ⟨ca, s3, k3, z3⟩ := bindOk z2
  obtain ⟨hs3, hca⟩ := getAppArgs_run p2.ok (denote_ext hcb p2.ext) k3
  rw [hs3] at z3
  obtain ⟨ro, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hro⟩ := allM_E_pstep (F := fun a => !a.mentionsConst TP)
    (fun st => denoteN st.ns T = some TP) (fun hx h => denoteN_ext h hx)
    (by
      intro a aP t0 t1 b hok0 hq0 ha hrun0
      obtain ⟨m, t2, q1, w1⟩ := bindOk hrun0
      obtain ⟨o1, hm⟩ := mentionsConst_spec T TP a aP t0 t2 m hok0 ⟨hq0, ha⟩ q1
      obtain ⟨rfl, rfl⟩ := pureOk w1
      exact ⟨o1, by rw [hm]⟩)
    _ _ s2 s4 ro p2.ok (denoteN_ext hT p2.ext) (denoteEList_drop hca nP) k4
  rw [recCtorKinds_some hsp', ← hc2]
  rw [hro] at z4
  split at z4
  case isTrue hc =>
    obtain ⟨rfl, rfl⟩ := pureOk z4
    refine ⟨p2.trans p4, ?_⟩
    rw [if_pos hc]
    exact ⟨_, rfl, hksm⟩
  case isFalse hc =>
    obtain ⟨rfl, rfl⟩ := pureOk z4
    refine ⟨p2.trans p4, ?_⟩
    rw [if_neg hc]
    refine ⟨_, rfl, ?_⟩
    show (ks.map _).map kindOf = _
    rw [← hksm]
    simp only [List.map_map]
    rfl

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
  intro s₀ s' r hok hte hrun
  simp only [Arena.structTeleAt] at hrun
  have hlen : tele.length = teleP.length := denoteBinders_length hte
  obtain ⟨hstep, hrel⟩ := mapM_pstep (β := EIdx × BinderMeta) (γ := Expr × BinderMeta) _
    (fun k => (ConLeche.structIdxAt nF o i l k (teleP.getD k default).1,
      (⟨pw⟩ : BinderMeta)))
    (fun st b c => denoteE st b.1 = some c.1 ∧ b.2 = c.2)
    (fun k st => denoteE st (tele.getD k default).1 = some (teleP.getD k default).1)
    (fun hx h => ⟨denote_ext h.1 hx, h.2⟩) (fun hx h => denote_ext h hx)
    (by
      intro k s₀ s' b hok hk hrun
      obtain ⟨x, s1, k1, hz⟩ := bindOk hrun
      obtain ⟨p1, hx⟩ := structIdxAt_spec nF o i l k _ _ s₀ s1 x hok hk k1
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨p1, hx, rfl⟩)
    (List.range tele.length) s₀ s' r hok
    (fun k hk => denoteBinders_getD hte (List.mem_range.mp hk)) hrun
  refine ⟨hstep, ?_⟩
  show denoteBinders _ r = some (ConLeche.structTeleAt nF o i l pw teleP)
  rw [ConLeche.structTeleAt, ← hlen]
  exact ListRel.toBinders hrel

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

/-- con-leche: none — `structIdxAt` mapped over a denoting handle list. -/
theorem structIdxAt_mapM (nF o i l m : Nat) :
    ∀ (idx : List EIdx) (idxP : List Expr) (s₀ s' : AState) (r : List EIdx),
      StateOK s₀ → Frontend.denoteEList s₀.store idx = some idxP →
      idx.mapM (fun e => Arena.structIdxAt nF o i l m e) s₀ = .ok (r, s') →
      PStep s₀ s' ∧
        Frontend.denoteEList s'.store r = some (idxP.map (ConLeche.structIdxAt nF o i l m)) := by
  intro idx
  induction idx with
  | nil =>
    intro idxP s₀ s' r hok h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons e es ih =>
    intro idxP s₀ s' r hok h hrun
    simp only [Frontend.denoteEList] at h
    cases he : denoteE s₀.store e with
    | none => rw [he] at h; simp at h
    | some eP =>
      cases hes : Frontend.denoteEList s₀.store es with
      | none => rw [he, hes] at h; simp at h
      | some esP =>
        rw [he, hes] at h
        obtain rfl := (Option.some.inj h).symm
        simp only [List.mapM_cons] at hrun
        obtain ⟨x, s1, k1, z1⟩ := bindOk hrun
        obtain ⟨p1, hx⟩ := structIdxAt_spec nF o i l m e eP s₀ s1 x hok he k1
        obtain ⟨xs, s2, k2, z2⟩ := bindOk z1
        obtain ⟨p2, hxs⟩ := ih esP s1 s2 xs p1.ok (denoteEList_ext p1.ext _ _ hes) k2
        obtain ⟨rfl, rfl⟩ := pureOk z2
        refine ⟨p1.trans p2, ?_⟩
        simp only [Frontend.denoteEList, List.map_cons, denote_ext hx p2.ext, hxs]

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrc, hrl, hte, hidx⟩ := hpre
  have hlen : tele.length = teleP.length := denoteBinders_length hte
  simp only [Arena.structIhApp] at hrun
  obtain ⟨hd, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hhd⟩ := internConstE_run hok hrc hrl k1
  obtain ⟨ps, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hps⟩ := structRecPrefixAt_spec nP n nF tele.length s1 s2 ps p1.ok trivial k2
  obtain ⟨ix, s3, k3, z3⟩ := bindOk z2
  obtain ⟨p3, hix⟩ := structIdxAt_mapM nF (n + 1) i 0 tele.length idx idxP s2 s3 ix p2.ok
    (denoteEList_ext (p1.ext.trans p2.ext) _ _ hidx) k3
  obtain ⟨fv, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hfv⟩ := internBVarE_run p3.ok k4
  obtain ⟨tv, s5, k5, z5⟩ := bindOk z4
  obtain ⟨p5, htv⟩ := structTeleVars_spec tele.length s4 s5 tv p4.ok trivial k5
  obtain ⟨fa, s6, k6, z6⟩ := bindOk z5
  obtain ⟨p6, hfa⟩ := mkAppN_run tv _ p5.ok (denote_ext hfv p5.ext) htv k6
  obtain ⟨bd, s7, k7, z7⟩ := bindOk z6
  have x16 : Ext s1.store s6.store :=
    p2.ext.trans (p3.ext.trans (p4.ext.trans (p5.ext.trans p6.ext)))
  have hargs : Frontend.denoteEList s6.store (ps ++ ix ++ [fa]) = some
      (ConLeche.structRecPrefixAt nP n nF tele.length ++
        idxP.map (ConLeche.structIdxAt nF (n + 1) i 0 tele.length) ++
        [Expr.mkAppN (.bvar (nF - 1 - i + tele.length))
          (ConLeche.structTeleVars tele.length)]) :=
    denoteEList_append (denoteEList_append
      (denoteEList_ext (p3.ext.trans (p4.ext.trans (p5.ext.trans p6.ext))) _ _ hps)
      (denoteEList_ext (p4.ext.trans (p5.ext.trans p6.ext)) _ _ hix))
      (by simp only [Frontend.denoteEList, hfa])
  obtain ⟨p7, hbd⟩ := mkAppN_run _ _ p6.ok (denote_ext hhd x16) hargs k7
  obtain ⟨tl, s8, k8, z8⟩ := bindOk z7
  have x07 : Ext s₀.store s7.store := p1.ext.trans (x16.trans p7.ext)
  obtain ⟨p8, htl⟩ := structTeleAt_spec nF (n + 1) i 0 pw tele teleP s7 s8 tl p7.ok
    (denoteBinders_ext x07 _ _ hte) k8
  obtain ⟨p9, hr⟩ := mkLamsOf_spec tl _ bd _ s8 s' r p8.ok
    ⟨htl, denote_ext hbd p8.ext⟩ z8
  refine ⟨p1.trans (p2.trans (p3.trans (p4.trans (p5.trans (p6.trans (p7.trans
    (p8.trans p9))))))), ?_⟩
  show denoteE _ r = _
  rw [hr, ConLeche.structIhApp, hlen]

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrc, hrl, hcty⟩ := hpre
  simp only [Arena.structRuleBodyR] at hrun
  obtain ⟨hd, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hhd⟩ := internBVarE_run hok k1
  obtain ⟨fs, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hfs⟩ := bvarsDesc_spec nF s1 s2 fs p1.ok trivial k2
  obtain ⟨ihs, s3, k3, z3⟩ := bindOk z2
  obtain ⟨p3, hihs⟩ := mapM_pstep (β := EIdx) (γ := Expr) _
    (fun i => ConLeche.structIhApp recCP rlvlsP pw nP n nF i
      (ConLeche.structFieldTeleOf ctyP nP nF i) (ConLeche.structFieldIdxOf ctyP nP nF i))
    (fun st b c => denoteE st b = some c)
    (fun i st => i < nF ∧ denoteN st.ns recC = some recCP ∧
      denoteLs st.lss rlvls = some rlvlsP ∧ denoteE st cty = some ctyP)
    (fun hx h => denote_ext h hx)
    (fun hx h => ⟨h.1, denoteN_ext h.2.1 hx, denoteLs_ext h.2.2.1 hx,
      denote_ext h.2.2.2 hx⟩)
    (by
      intro i s₀ s' b hok hP hrun
      obtain ⟨hi, hrc, hrl, hcty⟩ := hP
      obtain ⟨te, t1, q1, w1⟩ := bindOk hrun
      obtain ⟨o1, hte⟩ := structFieldTeleOf_spec cty ctyP nP nF i hi s₀ t1 te hok hcty q1
      obtain ⟨ix, t2, q2, w2⟩ := bindOk w1
      obtain ⟨o2, hix⟩ := structFieldIdxOf_spec cty ctyP nP nF i hi t1 t2 ix o1.ok
        (denote_ext hcty o1.ext) q2
      obtain ⟨o3, hb⟩ := structIhApp_spec recC recCP rlvls rlvlsP pw nP n nF i te _ ix _
        t2 s' b o2.ok ⟨denoteN_ext hrc (o1.ext.trans o2.ext),
          denoteLs_ext hrl (o1.ext.trans o2.ext), denoteBinders_ext o2.ext _ _ hte, hix⟩ w2
      exact ⟨o1.trans (o2.trans o3), hb⟩)
    recIdx s2 s3 ihs p2.ok
    (fun i hi => ⟨hri i hi, denoteN_ext hrc (p1.ext.trans p2.ext),
      denoteLs_ext hrl (p1.ext.trans p2.ext), denote_ext hcty (p1.ext.trans p2.ext)⟩) k3
  have hargs := denoteEList_append (denoteEList_ext p3.ext _ _ hfs) (ListRel.toEList hihs)
  obtain ⟨p4, hr⟩ := mkAppN_run _ _ p3.ok (denote_ext hhd (p2.ext.trans p3.ext)) hargs z3
  refine ⟨p1.trans (p2.trans (p3.trans p4)), ?_⟩
  show denoteE _ r = _
  have hps : ConLeche.structPsAt 0 nF =
      (List.range nF).map fun k => Expr.bvar (nF - 1 - k) := by
    simp only [ConLeche.structPsAt]
    exact bvarRange_congr (fun k => by omega)
  rw [hr, ConLeche.structRuleBodyR, hps]

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
  induction is generalizing l with
  | nil =>
    intro s₀ s' r hok hpre hrun
    simp only [Arena.structIhPis] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, hpre.2⟩
  | cons i is ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hcty, hbody⟩ := hpre
    have hi : i < nF := his i (by simp)
    simp only [Arena.structIhPis] at hrun
    obtain ⟨te, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hte⟩ := structFieldTeleOf_spec cty ctyP nP nF i hi s₀ s1 te hok hcty k1
    have hlen : te.length = (ConLeche.structFieldTeleOf ctyP nP nF i).length :=
      denoteBinders_length hte
    obtain ⟨ix, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hix⟩ := structFieldIdxOf_spec cty ctyP nP nF i hi s1 s2 ix p1.ok
      (denote_ext hcty p1.ext) k2
    obtain ⟨mo, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hmo⟩ := internBVarE_run p2.ok k3
    obtain ⟨ix', s4, k4, z4⟩ := bindOk z3
    obtain ⟨p4, hix'⟩ := structIdxAt_mapM nF o i l te.length ix _ s3 s4 ix' p3.ok
      (denoteEList_ext p3.ext _ _ hix) k4
    obtain ⟨fv, s5, k5, z5⟩ := bindOk z4
    obtain ⟨p5, hfv⟩ := internBVarE_run p4.ok k5
    obtain ⟨tv, s6, k6, z6⟩ := bindOk z5
    obtain ⟨p6, htv⟩ := structTeleVars_spec te.length s5 s6 tv p5.ok trivial k6
    obtain ⟨fa, s7, k7, z7⟩ := bindOk z6
    obtain ⟨p7, hfa⟩ := mkAppN_run tv _ p6.ok (denote_ext hfv p6.ext) htv k7
    obtain ⟨cc, s8, k8, z8⟩ := bindOk z7
    have hargs := denoteEList_append
      (denoteEList_ext (p5.ext.trans (p6.ext.trans p7.ext)) _ _ hix')
      (show Frontend.denoteEList s7.store [fa] = some [_] by
        simp only [Frontend.denoteEList, hfa]; rfl)
    obtain ⟨p8, hcc⟩ := mkAppN_run _ _ p7.ok
      (denote_ext hmo (p4.ext.trans (p5.ext.trans (p6.ext.trans p7.ext)))) hargs k8
    obtain ⟨tl, s9, k9, z9⟩ := bindOk z8
    obtain ⟨p9, htl⟩ := structTeleAt_spec nF o i l pw te _ s8 s9 tl p8.ok
      (denoteBinders_ext (p2.ext.trans (p3.ext.trans (p4.ext.trans (p5.ext.trans
        (p6.ext.trans (p7.ext.trans p8.ext)))))) _ _ hte) k9
    obtain ⟨dm, s10, k10, z10⟩ := bindOk z9
    obtain ⟨p10, hdm⟩ := mkPisOf_spec tl _ cc _ s9 s10 dm p9.ok
      ⟨htl, denote_ext hcc p9.ext⟩ k10
    have q10 : PStep s₀ s10 := p1.trans (p2.trans (p3.trans (p4.trans (p5.trans
      (p6.trans (p7.trans (p8.trans (p9.trans p10))))))))
    obtain ⟨rs, s11, k11, z11⟩ := bindOk z10
    obtain ⟨p11, hrs⟩ := ih (l + 1) (fun j hj => his j (by simp [hj])) s10 s11 rs q10.ok
      ⟨denote_ext hcty q10.ext, denote_ext hbody q10.ext⟩ k11
    obtain ⟨p12, hr⟩ := internForallEE_run p11.ok (denote_ext hdm p11.ext) hrs z11
    refine ⟨q10.trans (p11.trans p12), ?_⟩
    show denoteE _ r = _
    rw [hr, ConLeche.structIhPis, ← hlen]

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hC, hlps, hcty⟩ := hpre
  simp only [Arena.structMinorTyR] at hrun
  obtain ⟨q, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hq⟩ := stripPis_pstep hok hcty k1
  rw [hs1] at z1
  rcases q with _ | ⟨qbs, q2⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨PStep.refl hok, ?_⟩
    show _ = none
    simp only [ConLeche.structMinorTyR, stripPis_none hq, Option.bind_none]
  obtain ⟨qxs, q2P, hq1, -, hq2⟩ := denoteBP_someB hq
  obtain ⟨rq, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hrq⟩ := stripPis_pstep hok hq2 k2
  rw [hs2] at z2
  rcases rq with _ | ⟨rbs, r2⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨PStep.refl hok, ?_⟩
    show _ = none
    simp only [ConLeche.structMinorTyR, hq1, stripPis_none hrq, Option.bind_some,
      Option.bind_none]
  obtain ⟨rxs, r2P, hr1, -, hr2⟩ := denoteBP_someB hrq
  obtain ⟨mo, s3, k3, z3⟩ := bindOk z2
  obtain ⟨p3, hmo⟩ := internBVarE_run hok k3
  obtain ⟨ra, s4, k4, z4⟩ := bindOk z3
  obtain ⟨hs4, hra⟩ := getAppArgs_run p3.ok (denote_ext hr2 p3.ext) k4
  rw [hs4] at z4
  obtain ⟨ix, s5, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hix⟩ := mapM_E_pstep (F := fun e => e.liftLooseBVars o nF)
    (fun e eP t0 t1 x hok0 he hx => liftFast_pstep hok0 he hx)
    _ _ s3 s5 ix p3.ok (denoteEList_drop hra nP) k5
  obtain ⟨sp, s6, k6, z6⟩ := bindOk z5
  obtain ⟨p6, hsp⟩ := structCtorSpineAt_spec C CP lps lpsP o nP nF s5 s6 sp p5.ok
    ⟨denoteN_ext hC (p3.ext.trans p5.ext), denoteNListE_ext (p3.ext.trans p5.ext) _ _ hlps⟩ k6
  obtain ⟨c0, s7, k7, z7⟩ := bindOk z6
  have hargs := denoteEList_append (denoteEList_ext p6.ext _ _ hix)
    (show Frontend.denoteEList s6.store [sp] = some [_] by
      simp only [Frontend.denoteEList, hsp]; rfl)
  obtain ⟨p7, hc0⟩ := mkAppN_run _ _ p6.ok (denote_ext hmo (p5.ext.trans p6.ext)) hargs k7
  obtain ⟨c1, s8, k8, z8⟩ := bindOk z7
  obtain ⟨p8, hc1⟩ := liftFast_pstep p7.ok hc0 k8
  have q8 : PStep s₀ s8 := p3.trans (p5.trans (p6.trans (p7.trans p8)))
  obtain ⟨inn, s9, k9, z9⟩ := bindOk z8
  obtain ⟨p9, hinn⟩ := structIhPis_spec nF o nP pw cty ctyP recIdx 0 c1 _ hri s8 s9 inn
    p8.ok ⟨denote_ext hcty q8.ext, hc1⟩ k9
  obtain ⟨lf, s10, k10, z10⟩ := bindOk z9
  obtain ⟨p10, hlf⟩ := liftFast_pstep p9.ok (denote_ext hq2 (q8.ext.trans p9.ext)) k10
  obtain ⟨p11, hr⟩ := replacePisPw_spec pw nF lf inn _ _ s10 s' r p10.ok
    ⟨hlf, denote_ext hinn p10.ext⟩ z10
  refine ⟨q8.trans (p9.trans (p10.trans p11)), ?_⟩
  simp only [ConLeche.structMinorTyR, hq1, hr1, Option.bind_some]
  exact hr

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
  induction cs generalizing csP o with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨_, hcs4, hbody⟩ := hpre
    simp only [denoteCtors4, Option.some.injEq] at hcs4
    subst hcs4
    simp only [Arena.structMinorsPisR] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, _, rfl, hbody⟩
  | cons c cs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hlps, hcs4, hbody⟩ := hpre
    obtain ⟨C, nF, cty, recIdx⟩ := c
    simp only [denoteCtors4] at hcs4
    cases hC : denoteN s₀.store.ns C with
    | none => rw [hC] at hcs4; simp at hcs4
    | some CP =>
    cases hcty : denoteE s₀.store cty with
    | none => rw [hC, hcty] at hcs4; simp at hcs4
    | some ctyP =>
    cases hrest : denoteCtors4 s₀.store cs with
    | none => rw [hC, hcty, hrest] at hcs4; simp at hcs4
    | some restP =>
    rw [hC, hcty, hrest] at hcs4
    obtain rfl := (Option.some.inj hcs4).symm
    have hri : ∀ i ∈ recIdx, i < nF := hcs (CP, nF, ctyP, recIdx) (by simp)
    simp only [Arena.structMinorsPisR] at hrun
    obtain ⟨mq, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hmq⟩ := structMinorTyR_spec C CP lps lpsP nP nF o pw cty ctyP recIdx hri
      s₀ s1 mq hok ⟨hC, hlps, hcty⟩ k1
    cases mq with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      show _ = none
      simp only [ConLeche.structMinorsPisR, show ConLeche.structMinorTyR CP lpsP nP nF o pw ctyP recIdx
        = none from hmq, Option.bind_none]
    | some mty =>
    obtain ⟨mtyP, hmP, hmty⟩ := hmq
    obtain ⟨rq, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hrq⟩ := ih restP (o + 1) (fun c hc => hcs c (by simp [hc])) s1 s2 rq p1.ok
      ⟨denoteNListE_ext p1.ext _ _ hlps, denoteCtors4_ext p1.ext _ _ hrest,
        denote_ext hbody p1.ext⟩ k2
    cases rq with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨p1.trans p2, ?_⟩
      show _ = none
      simp only [ConLeche.structMinorsPisR, hmP, Option.bind_some,
        show ConLeche.structMinorsPisR lpsP nP pw restP (o + 1) bodyP = none from hrq, Option.map_none]
    | some rest =>
    obtain ⟨restP', hrP, hrd⟩ := hrq
    obtain ⟨x, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hx⟩ := internForallEE_run p2.ok (denote_ext hmty p2.ext) hrd k3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨p1.trans (p2.trans p3), _, ?_, hx⟩
    simp only [ConLeche.structMinorsPisR, hmP, hrP, Option.bind_some, Option.map_some]

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
  induction cs generalizing csP o with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨_, hcs4, hbody⟩ := hpre
    simp only [denoteCtors4, Option.some.injEq] at hcs4
    subst hcs4
    simp only [Arena.structMinorsLamsR] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, _, rfl, hbody⟩
  | cons c cs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hlps, hcs4, hbody⟩ := hpre
    obtain ⟨C, nF, cty, recIdx⟩ := c
    simp only [denoteCtors4] at hcs4
    cases hC : denoteN s₀.store.ns C with
    | none => rw [hC] at hcs4; simp at hcs4
    | some CP =>
    cases hcty : denoteE s₀.store cty with
    | none => rw [hC, hcty] at hcs4; simp at hcs4
    | some ctyP =>
    cases hrest : denoteCtors4 s₀.store cs with
    | none => rw [hC, hcty, hrest] at hcs4; simp at hcs4
    | some restP =>
    rw [hC, hcty, hrest] at hcs4
    obtain rfl := (Option.some.inj hcs4).symm
    have hri : ∀ i ∈ recIdx, i < nF := hcs (CP, nF, ctyP, recIdx) (by simp)
    simp only [Arena.structMinorsLamsR] at hrun
    obtain ⟨mq, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hmq⟩ := structMinorTyR_spec C CP lps lpsP nP nF o pw cty ctyP recIdx hri
      s₀ s1 mq hok ⟨hC, hlps, hcty⟩ k1
    cases mq with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      show _ = none
      simp only [ConLeche.structMinorsLamsR, show ConLeche.structMinorTyR CP lpsP nP nF o pw ctyP recIdx
        = none from hmq, Option.bind_none]
    | some mty =>
    obtain ⟨mtyP, hmP, hmty⟩ := hmq
    obtain ⟨rq, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hrq⟩ := ih restP (o + 1) (fun c hc => hcs c (by simp [hc])) s1 s2 rq p1.ok
      ⟨denoteNListE_ext p1.ext _ _ hlps, denoteCtors4_ext p1.ext _ _ hrest,
        denote_ext hbody p1.ext⟩ k2
    cases rq with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨p1.trans p2, ?_⟩
      show _ = none
      simp only [ConLeche.structMinorsLamsR, hmP, Option.bind_some,
        show ConLeche.structMinorsLamsR lpsP nP pw restP (o + 1) bodyP = none from hrq, Option.map_none]
    | some rest =>
    obtain ⟨restP', hrP, hrd⟩ := hrq
    obtain ⟨x, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hx⟩ := internLamE_run p2.ok (denote_ext hmty p2.ext) hrd k3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨p1.trans (p2.trans p3), _, ?_, hx⟩
    simp only [ConLeche.structMinorsLamsR, hmP, hrP, Option.bind_some, Option.map_some]

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, helim, htty, hcs4⟩ := hpre
  have hn : ctors.length = ctorsP.length := denoteCtors4_length hcs4
  simp only [Arena.structRecTyR] at hrun
  obtain ⟨l, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hl⟩ := structElimLevel_spec elim elimP large s₀ s1 l hok helim k1
  obtain ⟨u, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hu⟩ := readLevel_run k2
  rw [hs2] at z2
  have hu' : u = ConLeche.structElimLevel elimP large := by
    rw [hl] at hu; exact (Option.some.inj hu).symm
  subst hu'
  obtain ⟨q, s3, k3, z3⟩ := bindOk z2
  obtain ⟨hs3, hq⟩ := stripPis_pstep p1.ok (denote_ext htty p1.ext) k3
  rw [hs3] at z3
  rcases q with _ | ⟨qbs, q2⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨p1, ?_⟩
    show _ = none
    simp only [ConLeche.structRecTyR, stripPis_none hq, Option.bind_none]
  obtain ⟨qxs, q2P, hq1, -, hq2⟩ := denoteBP_someB hq
  obtain ⟨mt, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hmt⟩ := structMotiveTyI_spec T TP lps lpsP nP nIdx l _ q2 q2P s1 s4 mt p1.ok
    ⟨denoteN_ext hT p1.ext, denoteNListE_ext p1.ext _ _ hlps, hl, hq2⟩ k4
  cases mt with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z4
    refine ⟨p1.trans p4, ?_⟩
    show _ = none
    simp only [ConLeche.structRecTyR, hq1, Option.bind_some,
      show ConLeche.structMotiveTyI TP lpsP nP nIdx (ConLeche.structElimLevel elimP large) q2P
        = none from hmt, Option.bind_none]
  | some motiveTy =>
  obtain ⟨mtP, hmP, hmd⟩ := hmt
  have q4 : PStep s₀ s4 := p1.trans p4
  obtain ⟨fam, s5, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hfam⟩ := structFamI_spec T TP lps lpsP nP nIdx (ctors.length + 1) 0 s4 s5 fam
    p4.ok ⟨denoteN_ext hT q4.ext, denoteNListE_ext q4.ext _ _ hlps⟩ k5
  obtain ⟨mv, s6, k6, z6⟩ := bindOk z5
  obtain ⟨p6, hmv⟩ := internBVarE_run p5.ok k6
  obtain ⟨iv, s7, k7, z7⟩ := bindOk z6
  obtain ⟨p7, hiv⟩ := structPsAt_spec 1 nIdx s6 s7 iv p6.ok trivial k7
  obtain ⟨b0, s8, k8, z8⟩ := bindOk z7
  obtain ⟨p8, hb0⟩ := internBVarE_run p7.ok k8
  obtain ⟨cc, s9, k9, z9⟩ := bindOk z8
  have hargs := denoteEList_append (denoteEList_ext p8.ext _ _ hiv)
    (show Frontend.denoteEList s8.store [b0] = some [_] by
      simp only [Frontend.denoteEList, hb0]; rfl)
  obtain ⟨p9, hcc⟩ := mkAppN_run _ _ p8.ok (denote_ext hmv (p7.ext.trans p8.ext)) hargs k9
  obtain ⟨mb, s10, k10, z10⟩ := bindOk z9
  obtain ⟨p10, hmb⟩ := internForallEE_run p9.ok
    (denote_ext hfam (p6.ext.trans (p7.ext.trans (p8.ext.trans p9.ext)))) hcc k10
  have q10 : PStep s₀ s10 := q4.trans (p5.trans (p6.trans (p7.trans (p8.trans
    (p9.trans p10)))))
  have x110 : Ext s1.store s10.store := p4.ext.trans (p5.ext.trans (p6.ext.trans
    (p7.ext.trans (p8.ext.trans (p9.ext.trans p10.ext)))))
  obtain ⟨lf, s11, k11, z11⟩ := bindOk z10
  obtain ⟨p11, hlf⟩ := liftFast_pstep p10.ok (denote_ext hq2 x110) k11
  obtain ⟨mj, s12, k12, z12⟩ := bindOk z11
  obtain ⟨p12, hmj⟩ := replacePisPw_spec _ nIdx lf mb _ _ s11 s12 mj p11.ok
    ⟨hlf, denote_ext hmb p11.ext⟩ k12
  have q12 : PStep s₀ s12 := q10.trans (p11.trans p12)
  cases mj with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z12
    simp only [ROp] at hmj
    refine ⟨q12, ?_⟩
    show _ = none
    simp only [ConLeche.structRecTyR, hq1, hmP, Option.bind_some, ← hn, hmj,
      Option.bind_none]
  | some major =>
  obtain ⟨majP, hmjP, hmjd⟩ := hmj
  obtain ⟨mn, s13, k13, z13⟩ := bindOk z12
  obtain ⟨p13, hmn⟩ := structMinorsPisR_spec lps lpsP nP _ ctors ctorsP 1 major majP hcs
    s12 s13 mn p12.ok ⟨denoteNListE_ext q12.ext _ _ hlps, denoteCtors4_ext q12.ext _ _ hcs4,
      hmjd⟩ k13
  cases mn with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z13
    simp only [ROp] at hmn
    refine ⟨q12.trans p13, ?_⟩
    show _ = none
    simp only [ConLeche.structRecTyR, hq1, hmP, Option.bind_some, ← hn, hmjP, hmn,
      Option.bind_none]
  | some minors =>
  obtain ⟨mnP, hmnP, hmnd⟩ := hmn
  obtain ⟨bd, s14, k14, z14⟩ := bindOk z13
  have x413 : Ext s4.store s13.store := p5.ext.trans (p6.ext.trans (p7.ext.trans
    (p8.ext.trans (p9.ext.trans (p10.ext.trans (p11.ext.trans (p12.ext.trans p13.ext)))))))
  obtain ⟨p14, hbd⟩ := internForallEE_run p13.ok (denote_ext hmd x413) hmnd k14
  have q14 : PStep s₀ s14 := q12.trans (p13.trans p14)
  obtain ⟨p15, hr⟩ := replacePisPw_spec _ nP tty bd ttyP _ s14 s' r p14.ok
    ⟨denote_ext htty q14.ext, hbd⟩ z14
  refine ⟨q14.trans p15, ?_⟩
  simp only [ConLeche.structRecTyR, hq1, hmP, Option.bind_some, ← hn, hmjP, hmnP]
  exact hr

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, helim, htty, hcs4, hrc, hrl⟩ := hpre
  have hn : ctors.length = ctorsP.length := denoteCtors4_length hcs4
  simp only [Arena.structRecRhsR] at hrun
  obtain ⟨l, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hl⟩ := structElimLevel_spec elim elimP large s₀ s1 l hok helim k1
  obtain ⟨u, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hu⟩ := readLevel_run k2
  rw [hs2] at z2
  have hu' : u = ConLeche.structElimLevel elimP large := by
    rw [hl] at hu; exact (Option.some.inj hu).symm
  subst hu'
  obtain ⟨hgn, hgs⟩ := denoteCtors4_getElem? hcs4 j
  cases hcj : ctors[j]? with
  | none =>
    rw [hcj] at z2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1, ?_⟩
    show _ = none
    simp only [ConLeche.structRecRhsR, hgn.mp hcj]
  | some cj =>
  obtain ⟨Cj, nF, cty, recIdx⟩ := cj
  obtain ⟨CjP, ctyP, hcjP, -, hcty⟩ := hgs Cj nF cty recIdx hcj
  have hri : ∀ i ∈ recIdx, i < nF :=
    hcs (CjP, nF, ctyP, recIdx) (List.mem_of_getElem? hcjP)
  rw [hcj] at z2
  dsimp only at z2
  obtain ⟨q, s3, k3, z3⟩ := bindOk z2
  obtain ⟨hs3, hq⟩ := stripPis_pstep p1.ok (denote_ext htty p1.ext) k3
  rw [hs3] at z3
  rcases q with _ | ⟨qbs, q2⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨p1, ?_⟩
    show _ = none
    simp only [ConLeche.structRecRhsR, hcjP, stripPis_none hq, Option.bind_none]
  obtain ⟨qxs, q2P, hq1, -, hq2⟩ := denoteBP_someB hq
  obtain ⟨mt, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hmt⟩ := structMotiveTyI_spec T TP lps lpsP nP nIdx l _ q2 q2P s1 s4 mt p1.ok
    ⟨denoteN_ext hT p1.ext, denoteNListE_ext p1.ext _ _ hlps, hl, hq2⟩ k4
  cases mt with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z4
    simp only [ROp] at hmt
    refine ⟨p1.trans p4, ?_⟩
    show _ = none
    simp only [ConLeche.structRecRhsR, hcjP, hq1, Option.bind_some, hmt, Option.bind_none]
  | some motiveTy =>
  obtain ⟨mtP, hmP, hmd⟩ := hmt
  have q4 : PStep s₀ s4 := p1.trans p4
  obtain ⟨cq, s5, k5, z5⟩ := bindOk z4
  obtain ⟨hs5, hcq⟩ := stripPis_pstep p4.ok (denote_ext hcty q4.ext) k5
  rw [hs5] at z5
  rcases cq with _ | ⟨cbs, c2⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z5
    refine ⟨q4, ?_⟩
    show _ = none
    simp only [ConLeche.structRecRhsR, hcjP, hq1, hmP, stripPis_none hcq, Option.bind_some,
      Option.bind_none]
  obtain ⟨cxs, c2P, hc1, -, hc2⟩ := denoteBP_someB hcq
  obtain ⟨bd, s6, k6, z6⟩ := bindOk z5
  obtain ⟨p6, hbd⟩ := structRuleBodyR_spec recC recCP rlvls rlvlsP _ nP ctors.length nF j
    recIdx cty ctyP hri s4 s6 bd p4.ok
    ⟨denoteN_ext hrc q4.ext, denoteLs_ext hrl q4.ext, denote_ext hcty q4.ext⟩ k6
  obtain ⟨lf, s7, k7, z7⟩ := bindOk z6
  obtain ⟨p7, hlf⟩ := liftFast_pstep p6.ok (denote_ext hc2 p6.ext) k7
  obtain ⟨inn, s8, k8, z8⟩ := bindOk z7
  obtain ⟨p8, hinn⟩ := pisToLamsPw_spec _ nF lf bd _ _ s7 s8 inn p7.ok
    ⟨hlf, denote_ext hbd p7.ext⟩ k8
  have q8 : PStep s₀ s8 := q4.trans (p6.trans (p7.trans p8))
  cases inn with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z8
    simp only [ROp] at hinn
    refine ⟨q8, ?_⟩
    show _ = none
    simp only [ConLeche.structRecRhsR, hcjP, hq1, hmP, hc1, Option.bind_some, ← hn, hinn,
      Option.bind_none]
  | some inner =>
  obtain ⟨innP, hinP, hind⟩ := hinn
  obtain ⟨mn, s9, k9, z9⟩ := bindOk z8
  obtain ⟨p9, hmn⟩ := structMinorsLamsR_spec lps lpsP nP _ ctors ctorsP 1 inner innP hcs
    s8 s9 mn p8.ok ⟨denoteNListE_ext q8.ext _ _ hlps, denoteCtors4_ext q8.ext _ _ hcs4,
      hind⟩ k9
  cases mn with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z9
    simp only [ROp] at hmn
    refine ⟨q8.trans p9, ?_⟩
    show _ = none
    simp only [ConLeche.structRecRhsR, hcjP, hq1, hmP, hc1, Option.bind_some, ← hn, hinP,
      hmn, Option.bind_none]
  | some minors =>
  obtain ⟨mnP, hmnP, hmnd⟩ := hmn
  obtain ⟨lm, s10, k10, z10⟩ := bindOk z9
  obtain ⟨p10, hlm⟩ := internLamE_run p9.ok
    (denote_ext hmd (p6.ext.trans (p7.ext.trans (p8.ext.trans p9.ext)))) hmnd k10
  have q10 : PStep s₀ s10 := q8.trans (p9.trans p10)
  obtain ⟨p11, hr⟩ := pisToLamsPw_spec _ nP tty lm ttyP _ s10 s' r p10.ok
    ⟨denote_ext htty q10.ext, hlm⟩ z10
  refine ⟨q10.trans p11, ?_⟩
  simp only [ConLeche.structRecRhsR, hcjP, hq1, hmP, hc1, Option.bind_some, ← hn, hinP, hmnP]
  exact hr

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrt, hrhs⟩ := hpre
  simp only [Arena.nativeRulePrefixOk] at hrun
  obtain ⟨lq, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hlq⟩ := stripLams_pstep hok hrhs k1
  rw [hs1] at z1
  obtain ⟨pq, s2, k2, z2⟩ := bindOk z1
  obtain ⟨hs2, hpq⟩ := stripPis_pstep hok hrt k2
  rw [hs2] at z2
  rcases lq with _ | ⟨rbs, rb⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨PStep.refl hok, ?_⟩
    show false = ConLeche.nativeRulePrefixOk recTyP nP n j nF rhsP
    have h0 : rhsP.stripLams (nP + 1 + n + nF) = none := (Option.some.inj hlq).symm
    simp only [ConLeche.nativeRulePrefixOk, h0]
  obtain ⟨rxs, rbP, hslP, hrbs, -⟩ := denoteBP_someB' hlq
  rcases pq with _ | ⟨tbs, tb⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨PStep.refl hok, ?_⟩
    show false = ConLeche.nativeRulePrefixOk recTyP nP n j nF rhsP
    simp only [ConLeche.nativeRulePrefixOk, hslP, stripPis_none hpq]
  obtain ⟨txs, tbP, hspP, htbs, -⟩ := denoteBP_someB hpq
  dsimp only at z2
  obtain ⟨po, s3, k3, z3⟩ := bindOk z2
  obtain ⟨p3, hpo⟩ := allM_pstep (g := fun i => match rxs[i]?, txs[i]? with
      | some b, some t => Expr.resetMeta b.1 == Expr.resetMeta t.1
      | _, _ => false)
    (fun _ st => denoteBinders st rbs = some rxs ∧ denoteBinders st tbs = some txs)
    (fun hx h => ⟨denoteBinders_ext hx _ _ h.1, denoteBinders_ext hx _ _ h.2⟩)
    (by
      intro i t0 t1 b hok0 hP hrun0
      obtain ⟨hr0, ht0⟩ := hP
      obtain ⟨hrA, hrB⟩ := denoteBinders_getElem? hr0 i
      obtain ⟨htA, htB⟩ := denoteBinders_getElem? ht0 i
      cases hri : rbs[i]? with
      | none =>
        rw [hri] at hrun0
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        exact ⟨PStep.refl hok0, by simp only [hrB hri]⟩
      | some bm =>
      obtain ⟨bb, bmm⟩ := bm
      obtain ⟨bP, hbP, hbd⟩ := hrA bb bmm hri
      cases hti : tbs[i]? with
      | none =>
        rw [hri, hti] at hrun0
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        exact ⟨PStep.refl hok0, by simp only [hbP, htB hti]⟩
      | some tm =>
      obtain ⟨tt, tmm⟩ := tm
      obtain ⟨tP, htP, htd⟩ := htA tt tmm hti
      rw [hri, hti] at hrun0
      obtain ⟨o1, hb⟩ := resetPair_pstep hok0 hbd htd hrun0
      exact ⟨o1, by simp only [hbP, htP, hb]⟩)
    (List.range (nP + 1 + n)) s₀ s3 po hok (fun _ _ => ⟨hrbs, htbs⟩) k3
  rw [hpo] at z3
  split at z3
  case isTrue hc =>
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨p3, ?_⟩
    show false = ConLeche.nativeRulePrefixOk recTyP nP n j nF rhsP
    simp only [Bool.not_eq_true'] at hc
    simp only [ConLeche.nativeRulePrefixOk, hslP, hspP]
    change false = (((List.range (nP + 1 + n)).all fun i => match rxs[i]?, txs[i]? with
        | some b, some t => Expr.resetMeta b.1 == Expr.resetMeta t.1
        | _, _ => false) && _)
    rw [hc]; rfl
  case isFalse hc =>
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
  have hrbs3 := denoteBinders_ext p3.ext _ _ hrbs
  have htbs3 := denoteBinders_ext p3.ext _ _ htbs
  obtain ⟨hmA, hmB⟩ := denoteBinders_getElem? htbs3 (nP + 1 + j)
  have hpre : ConLeche.nativeRulePrefixOk recTyP nP n j nF rhsP =
      (match txs[nP + 1 + j]? with
       | some mty =>
         (match (mty.1.liftLooseBVars (n - j) 0).stripPis nF with
          | some (fbs, _) =>
            (List.range nF).all fun i =>
              match rxs[nP + 1 + n + i]?, fbs[i]? with
              | some b, some f => Expr.resetMeta b.1 == Expr.resetMeta f.1
              | _, _ => false
          | none => false)
       | none => false) := by
    simp only [ConLeche.nativeRulePrefixOk, hslP, hspP]
    change (((List.range (nP + 1 + n)).all fun i => match rxs[i]?, txs[i]? with
        | some b, some t => Expr.resetMeta b.1 == Expr.resetMeta t.1
        | _, _ => false) && _) = _
    rw [hc]; rfl
  cases hm : tbs[nP + 1 + j]? with
  | none =>
    rw [hm] at z3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨p3, ?_⟩
    show false = _
    rw [hpre, hmB hm]
  | some mq =>
  obtain ⟨mt, mm⟩ := mq
  obtain ⟨mtP, hmP, hmd⟩ := hmA mt mm hm
  rw [hm] at z3
  dsimp only at z3
  obtain ⟨lf, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hlf⟩ := liftFast_pstep p3.ok hmd k4
  obtain ⟨fq, s5, k5, z5⟩ := bindOk z4
  obtain ⟨hs5, hfq⟩ := stripPis_pstep p4.ok hlf k5
  rw [hs5] at z5
  rcases fq with _ | ⟨fbs, fb⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z5
    refine ⟨p3.trans p4, ?_⟩
    show false = _
    rw [hpre, hmP]
    dsimp only
    rw [stripPis_none hfq]
  obtain ⟨fxs, fbP, hfP, hfbs, -⟩ := denoteBP_someB hfq
  dsimp only at z5
  obtain ⟨p6, hr⟩ := allM_pstep (g := fun i => match rxs[nP + 1 + n + i]?, fxs[i]? with
      | some b, some f => Expr.resetMeta b.1 == Expr.resetMeta f.1
      | _, _ => false)
    (fun _ st => denoteBinders st rbs = some rxs ∧ denoteBinders st fbs = some fxs)
    (fun hx h => ⟨denoteBinders_ext hx _ _ h.1, denoteBinders_ext hx _ _ h.2⟩)
    (by
      intro i t0 t1 b hok0 hP hrun0
      obtain ⟨hr0, hf0⟩ := hP
      obtain ⟨hrA, hrB⟩ := denoteBinders_getElem? hr0 (nP + 1 + n + i)
      obtain ⟨hfA, hfB⟩ := denoteBinders_getElem? hf0 i
      cases hri : rbs[nP + 1 + n + i]? with
      | none =>
        rw [hri] at hrun0
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        exact ⟨PStep.refl hok0, by simp only [hrB hri]⟩
      | some bm =>
      obtain ⟨bb, bmm⟩ := bm
      obtain ⟨bP, hbP, hbd⟩ := hrA bb bmm hri
      cases hfi : fbs[i]? with
      | none =>
        rw [hri, hfi] at hrun0
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        exact ⟨PStep.refl hok0, by simp only [hbP, hfB hfi]⟩
      | some fm =>
      obtain ⟨ff, fmm⟩ := fm
      obtain ⟨fP, hfP', hfd⟩ := hfA ff fmm hfi
      rw [hri, hfi] at hrun0
      obtain ⟨o1, hb⟩ := resetPair_pstep hok0 hbd hfd hrun0
      exact ⟨o1, by simp only [hbP, hfP', hb]⟩)
    (List.range nF) s4 s' r p4.ok
    (fun _ _ => ⟨denoteBinders_ext p4.ext _ _ hrbs3, hfbs⟩) z5
  refine ⟨p3.trans (p4.trans p6), ?_⟩
  show r = _
  rw [hpre, hmP]
  dsimp only
  rw [hfP, hr]

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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrc, hrl, hcs, hrh, hrt⟩ := hpre
  have hrlen : rhssP.length = rhss.length := denoteEList_len hrh
  simp only [Arena.nativeRulesOk] at hrun
  have e0 : (rhss.length == n && kinds.length == n) =
      (rhssP.length == n && (kinds.map (·.map kindOf)).length == n) := by
    rw [hrlen, List.length_map]
  rw [e0] at hrun
  split at hrun
  case isTrue hc =>
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show false = _
    simp only [Bool.not_eq_true'] at hc
    simp only [ConLeche.nativeRulesOk, hc, Bool.false_and]
  case isFalse hc =>
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
  obtain ⟨p1, hr⟩ := allM_pstep (g := fun j =>
      match rhssP[j]?, csP[j]?, (kinds.map (·.map kindOf))[j]? with
      | some rhs, some (cA, nF), some ks =>
        ks.length == nF &&
        (match rhs.stripLams (nP + 1 + n + nF) with
         | some (_, rbody) =>
           rbody == Expr.resetMeta (ConLeche.structRuleBodyR recCP rlvlsP pw nP n nF j
             (ConLeche.recIdxOf ks) (ConLeche.structFieldTeleOf cA.type nP nF)
             (ConLeche.structFieldIdxOf cA.type nP nF))
         | none => false) &&
        ConLeche.nativeRulePrefixOk recTyP nP n j nF rhs
      | _, _, _ => false)
    (fun _ st => denoteN st.ns recC = some recCP ∧ denoteLs st.lss rlvls = some rlvlsP ∧
      denoteCtors st cs = some csP ∧ Frontend.denoteEList st rhss = some rhssP ∧
      denoteE st recTy = some recTyP)
    (fun hx h => ⟨denoteN_ext h.1 hx, denoteLs_ext h.2.1 hx, denoteCtors_ext hx _ _ h.2.2.1,
      denoteEList_ext hx _ _ h.2.2.2.1, denote_ext h.2.2.2.2 hx⟩)
    (by
      intro j t0 t1 b hok0 hP hrun0
      obtain ⟨hrc0, hrl0, hcs0, hrh0, hrt0⟩ := hP
      obtain ⟨hcA, hcB⟩ := denoteCtors_getElem? hcs0 j
      cases hrj : rhss[j]? with
      | none =>
        rw [hrj] at hrun0
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        refine ⟨PStep.refl hok0, ?_⟩
        have : rhssP[j]? = none := by
          rw [List.getElem?_eq_none_iff] at hrj ⊢
          rw [denoteEList_len hrh0]; exact hrj
        simp only [this]
      | some rhs =>
      obtain ⟨rhsP, hrjP, hrhs⟩ := ExprOps.denoteEList_getElem? rhss rhssP hrh0 j rhs hrj
      cases hcj : cs[j]? with
      | none =>
        rw [hrj, hcj] at hrun0
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        exact ⟨PStep.refl hok0, by simp only [hrjP, hcB hcj]⟩
      | some cq =>
      obtain ⟨cA, nF⟩ := cq
      obtain ⟨cAP, hcjP, hcA'⟩ := hcA cA nF hcj
      cases hkj : kinds[j]? with
      | none =>
        rw [hrj, hcj, hkj] at hrun0
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        exact ⟨PStep.refl hok0, by simp only [hrjP, hcjP, List.getElem?_map, hkj,
          Option.map_none]⟩
      | some ks =>
      rw [hrj, hcj, hkj] at hrun0
      dsimp only at hrun0
      have hkP : (kinds.map (·.map kindOf))[j]? = some (ks.map kindOf) := by
        simp only [List.getElem?_map, hkj, Option.map_some]
      show PStep t0 t1 ∧ b = _
      simp only [hrjP, hcjP, hkP, List.length_map]
      split at hrun0
      case isTrue hc1 =>
        obtain ⟨rfl, rfl⟩ := pureOk hrun0
        simp only [Bool.not_eq_true'] at hc1
        exact ⟨PStep.refl hok0, by simp only [hc1, Bool.false_and]⟩
      case isFalse hc1 =>
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hc1
      have hnF : ks.length = nF := by simpa using hc1
      have hri : ∀ i ∈ Arena.recIdxOf ks, i < nF := by
        intro i hi
        simp only [Arena.recIdxOf, List.mem_filter, List.mem_range] at hi
        omega
      have hty0 := denoteCV_type hcA'
      obtain ⟨lq, t2, q1, w1⟩ := bindOk hrun0
      obtain ⟨hs2, hlq⟩ := stripLams_pstep hok0 hrhs q1
      rw [hs2] at w1
      rcases lq with _ | ⟨lbs, rbody⟩
      · have h0 : rhsP.stripLams (nP + 1 + n + nF) = none := (Option.some.inj hlq).symm
        obtain ⟨y, t3, q2, w2⟩ := bindOk w1
        obtain ⟨rfl, rfl⟩ := pureOk q2
        obtain ⟨rfl, rfl⟩ := pureOk w2
        exact ⟨PStep.refl hok0, by simp only [h0, hnF, beq_self_eq_true, Bool.true_and,
          Bool.false_and]⟩
      obtain ⟨_, rbodyP, hslP, hrbd⟩ := denoteBP_some' hlq
      obtain ⟨wt, u1, v1, y1⟩ := bindOk w1
      obtain ⟨o1, hwt⟩ := structRuleBodyR_spec recC recCP rlvls rlvlsP pw nP n nF j
        (Arena.recIdxOf ks) cA.type cAP.type hri t0 u1 wt hok0 ⟨hrc0, hrl0, hty0⟩ v1
      obtain ⟨rw', u2, v2, y2⟩ := bindOk y1
      obtain ⟨o2, hrw⟩ := resetMeta_pstep o1.ok hwt v2
      obtain ⟨y, u3, v3, y3⟩ := bindOk y2
      obtain ⟨rfl, rfl⟩ := pureOk v3
      have hbeq := beq_ehandle_eq o2.ok.wf (denote_ext hrbd (o1.ext.trans o2.ext)) hrw
      rw [hbeq, recIdxOf_spec] at y3
      split at y3
      case isTrue hc2 =>
        obtain ⟨rfl, rfl⟩ := pureOk y3
        simp only [Bool.not_eq_true'] at hc2
        exact ⟨o1.trans o2, by simp only [hslP, hnF, beq_self_eq_true, hc2, Bool.true_and,
          Bool.false_and]⟩
      case isFalse hc2 =>
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hc2
        obtain ⟨p3, hb⟩ := nativeRulePrefixOk_spec recTy recTyP nP n j nF rhs rhsP _ t1 b
          o2.ok ⟨denote_ext hrt0 (o1.ext.trans o2.ext), denote_ext hrhs (o1.ext.trans o2.ext)⟩ y3
        exact ⟨o1.trans (o2.trans p3), by simp only [hslP, hnF, beq_self_eq_true, hc2,
          Bool.true_and, hb]⟩)
    (List.range n) s₀ s' r hok (fun _ _ => ⟨hrc, hrl, hcs, hrh, hrt⟩) hrun
  refine ⟨p1, ?_⟩
  show r = ConLeche.nativeRulesOk recCP rlvlsP pw nP n csP (kinds.map (·.map kindOf)) rhssP recTyP
  rw [hr]
  simp only [ConLeche.nativeRulesOk, hc, Bool.true_and]
  rfl

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
