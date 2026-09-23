/-
# `ConRon.Bridge.Inductives.ProjRule` — Theorem 1 for a projection function's pieces

Task #97-P3-Ind round 9.  `Arena/Inductives/Modeled.lean`'s `checkProjFn`
calls three twins that had no Theorem 1 anywhere: `checkProjShape` and
`checkProjRule` (`Arena/CheckerBase.lean`, twins of
`ConLeche/Kernel/CheckerBase.lean`'s) and `projFnRule` (`Arena/Core.lean`,
twin of `ConLeche/Kernel/CoreDefs.lean`'s).  This module states and proves
the three, so that `Bridge/Inductives/Modeled.lean`'s `checkProjFn_spec` is a
composition.

**`checkProjShape` and `checkProjRule` are CHECKER-tier twins** (they live in
`Arena/CheckerBase.lean`, beside the declaration checker's own stages) and
belong one tier down, in `Bridge/Checker/**`; they are written here because
this tier is their only consumer today.  DESIGN's round-9 section lists them
as candidates to move down.  Nothing in them reads this tier's own
definitions except the run-form helpers of `Bridge/Inductives/Rel.lean`.

`checkProjRule` also needs `Bridge/ExprOps/TelescopeF.lean`'s `InstListSpec`
at `coreWalkFuel` (the `…F` telescope twins take `instantiateListFast`'s
Theorem 1 as a record).  `Bridge/ExprOps/Subst.lean` has since proved
`instantiateListFast_spec`, so `instListSpec` below discharges the record for
every fuel; it belongs in `TelescopeF.lean`, which cannot import `Subst.lean`
without a cycle check nobody has run — another candidate to move.
-/
import ConRon.Bridge.Inductives.NativeInstall
import ConRon.Bridge.ExprOps.TelescopeF
import ConRon.Bridge.ExprOps.Subst
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.FastOps

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## `instantiateListFast`'s record, discharged -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast —
`Bridge/ExprOps/TelescopeF.lean`'s hypothesis record, discharged at
`Bridge/ExprOps/Subst.lean`'s `instantiateListFast_spec`: the record
quantifies the vector's denotation inside its answer relation, the theorem
names it in its precondition, and `denoteEList` is a function. -/
theorem instListSpec (fuel : Nat) : ExprOps.InstListSpec fuel := by
  refine ⟨fun s₁ e vs d hok hden hvs => ?_⟩
  obtain ⟨ws', hws'⟩ := Option.isSome_iff_exists.mp hvs
  have hvec : ExprOps.InstLVec s₁.store vs ws'.reverse := by
    simp only [ExprOps.InstLVec, List.reverse_reverse]; exact hws'
  refine Core.triple_mono
    (ExprOps.instantiateListFast_spec fuel s₁ e vs d ws'.reverse hok hvec hden) ?_
  rintro r s ⟨h1, h2, h3, h4, h5, -, h7⟩
  refine ⟨h1, h2, h3, h4, h5, fun x es hx hes => ?_⟩
  rw [hws'] at hes
  obtain rfl := Option.some.inj hes
  exact h7 x hx

/-! ## Small run forms -/

/-- con-leche: none — `xs.map Expr.fvarTypeD`, the arena's list helper, as a
run: read-only, and the answer denotes the mapped list. -/
theorem fvarTypeDs_run {s₀ : AState} (hok : StateOK s₀) :
    ∀ (hs : List EIdx) {xs : List Expr} {r : List EIdx} {s' : AState},
      Frontend.denoteEList s₀.store hs = some xs →
      Arena.fvarTypeDs hs s₀ = .ok (r, s') →
      s' = s₀ ∧ Frontend.denoteEList s₀.store r = some (xs.map Expr.fvarTypeD) := by
  intro hs
  induction hs with
  | nil =>
    intro xs r s' hxs hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hxs
    subst hxs
    simp only [Arena.fvarTypeDs] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨rfl, rfl⟩
  | cons h hs ih =>
    intro xs r s' hxs hrun
    obtain ⟨x, xs', hx, hxs', rfl⟩ := denoteEList_cons hxs
    simp only [Arena.fvarTypeDs] at hrun
    obtain ⟨t, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨rfl, ht⟩ := fvarTypeD_run hok hx k1
    obtain ⟨ts, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨rfl, hts⟩ := ih hxs' k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨rfl, ?_⟩
    simp only [Frontend.denoteEList, ht, hts, List.map_cons]

/-- con-leche: none — an `Option` handle's denotation at `some`. -/
theorem denoteEO_some_inv {st : EStore} {j : EIdx} {v : Option Expr}
    (h : denoteEO st (some j) = some v) : ∃ x, v = some x ∧ denoteE st j = some x := by
  simp only [denoteEO, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, rfl, hx⟩

/-- con-leche: none — an `Option` pair's denotation at `some`. -/
theorem denoteEP_some_inv {st : EStore} {ds : List EIdx} {e : EIdx}
    {v : Option (List Expr × Expr)}
    (h : ExprOps.denoteEP st (some (ds, e)) = some v) :
    ∃ xs x, v = some (xs, x) ∧ Frontend.denoteEList st ds = some xs ∧
      denoteE st e = some x := by
  simp only [ExprOps.denoteEP] at h
  cases h1 : Frontend.denoteEList st ds with
  | none => rw [h1] at h; simp at h
  | some xs =>
    cases h2 : denoteE st e with
    | none => rw [h1, h2] at h; simp at h
    | some x =>
      rw [h1, h2] at h
      exact ⟨xs, x, (Option.some.inj h).symm, rfl, rfl⟩

/-! ## The binder comparison (moved from `Modeled.lean`, round 9) -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux — the
range peeled at its TOP, which is the order the twin's recursion runs in. -/
theorem domsMatchAux_succ (g : Nat → Expr → Expr) (bs₁ bs₂ : List (Expr × BinderMeta))
    (o₁ o₂ k : Nat) :
    ConLeche.domsMatchAux g bs₁ bs₂ o₁ o₂ (k + 1) =
      (ConLeche.domsMatchAux g bs₁ bs₂ o₁ o₂ k &&
        (match bs₁[o₁ + k]?, bs₂[o₂ + k]? with
         | some b₁, some b₂ => b₁.1 == g k b₂.1
         | _, _ => false)) := by
  simp only [ConLeche.domsMatchAux, List.range_succ, List.all_append, List.all_cons,
    List.all_nil, Bool.and_true]
  rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux — **the
arena's binder comparison IS con-leche's at `g := fun _ e => e`**: the handle
arrays are the lists' `toArray`, and each handle comparison is
`beq_ehandle_eq`. -/
theorem domsMatchAux_eq {st : EStore} (hwf : StoreWF st)
    {bs₁ bs₂ : List (EIdx × BinderMeta)} {xs₁ xs₂ : List (Expr × BinderMeta)}
    (h1 : denoteBinders st bs₁ = some xs₁) (h2 : denoteBinders st bs₂ = some xs₂)
    (o₁ o₂ : Nat) : ∀ n, Arena.domsMatchAux bs₁.toArray bs₂.toArray o₁ o₂ n =
      ConLeche.domsMatchAux (fun _ e => e) xs₁ xs₂ o₁ o₂ n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [domsMatchAux_succ]
    have hA : Arena.domsMatchAux bs₁.toArray bs₂.toArray o₁ o₂ (k + 1) =
        (Arena.domsMatchAux bs₁.toArray bs₂.toArray o₁ o₂ k &&
          (match bs₁[o₁ + k]?, bs₂[o₂ + k]? with
           | some b₁, some b₂ => b₁.1 == b₂.1
           | _, _ => false)) := by
      simp only [Arena.domsMatchAux, List.range_succ, List.all_append, List.all_cons,
        List.all_nil, Bool.and_true, List.getElem?_toArray]
      rfl
    rw [hA, ih]
    congr 1
    obtain ⟨hA1, hB1⟩ := denoteBinders_getElem? h1 (o₁ + k)
    obtain ⟨hA2, hB2⟩ := denoteBinders_getElem? h2 (o₂ + k)
    cases hb1 : bs₁[o₁ + k]? with
    | none => simp [hB1 hb1]
    | some p1 =>
    obtain ⟨t1, m1⟩ := p1
    obtain ⟨t1P, hp1, hd1⟩ := hA1 t1 m1 hb1
    cases hb2 : bs₂[o₂ + k]? with
    | none => simp [hp1, hB2 hb2]
    | some p2 =>
    obtain ⟨t2, m2⟩ := p2
    obtain ⟨t2P, hp2, hd2⟩ := hA2 t2 m2 hb2
    simp only [hp1, hp2]
    exact beq_ehandle_eq hwf hd1 hd2

/-! ## `checkProjShape` -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:257-272 checkProjShape —
**stage 2b of a projection function, read-only**: both telescopes strip, and
the constructor's residual is a constant applied to exactly the parameters.
Every step (`stripPis` twice, `getAppArgs`, `getAppFn`, `view`) leaves the
state alone, so the frame is `PStep.refl`.

A CHECKER-tier twin (`Arena/CheckerBase.lean`); a candidate to move down. -/
theorem checkProjShape_spec (pty cty : EIdx) (ptyP ctyP : Expr) (nP nF : Nat) :
    PSpec (fun st => denoteE st pty = some ptyP ∧ denoteE st cty = some ctyP)
      (Arena.checkProjShape pty cty nP nF)
      (fun _ _ => (ConLeche.checkProjShape ptyP ctyP nP nF : CheckM Unit) = .ok ()) := by
  intro s₀ s' u hok hpre hrun
  obtain ⟨hp, hc⟩ := hpre
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkProjShape] at hrun
  obtain ⟨o1, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨rfl, ho1⟩ := stripPis_pstep hok hp k1
  rcases o1 with _ | ⟨bs1, e1⟩
  · exact absurd z1 (AM.Never.fail _ _ _ _)
  obtain ⟨xs1, x1, hx1, -⟩ := stripPis_some ho1
  obtain ⟨o2, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨rfl, ho2⟩ := stripPis_pstep hok hc k2
  rcases o2 with _ | ⟨bs2, cbody⟩
  · exact absurd z2 (AM.Never.fail _ _ _ _)
  obtain ⟨xs2, cbodyP, hx2, hcb⟩ := stripPis_some ho2
  obtain ⟨args, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨rfl, hargs⟩ := getAppArgs_run hok hcb k3
  obtain ⟨hlen, z4⟩ := AM.dunless_ok hnever z3
  replace z4 := AM.pure_bind_ok z4
  obtain ⟨hd, s₄, k4, z5⟩ := bindOk z4
  obtain ⟨rfl, hhd⟩ := getAppFn_run hok hcb k4
  obtain ⟨v, s₅, k5, z6⟩ := bindOk z5
  obtain ⟨rfl, hv⟩ := view_run k5
  have hlenP : cbodyP.getAppArgs.length = nP := by
    have := ExprOps.denoteEList_length _ _ hargs
    simp only [beq_iff_eq] at hlen
    omega
  cases v
  case const n us =>
    obtain ⟨-, rfl⟩ := pureOk z6
    refine ⟨PStep.refl hok, ?_⟩
    obtain ⟨nm, ls, hfn, -, -⟩ := denote_const_inv hok.wf hv hhd
    simp only [ConLeche.checkProjShape, hx1, hx2, bind, Except.bind, hfn]
    rw [if_pos (by simpa using hlenP)]
    rfl
  all_goals exact absurd z6 (AM.Never.fail _ _ _ _)

/-! ## `checkProjRule` -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule —
**stage 3 of a projection function**: the reduction rule, a λ over the
constructor telescope returning field `i`, annotated, scoped, shaped, its
domains the constructor's, and the two definitional frame pins.

The two scoping hypotheses are the pure run's own (`checkProjRule_wfimp`
takes the same two): the projection type is `checkProjTy`'s answer (closed by
its guard) and the constructor's type is a stored constant's (closed by
`EnvWF`).  They are what `checkDefEqList_bridge` needs of the two frame lists,
exactly as con-leche's `checkProjRuleS_sim` derives them.

A CHECKER-tier twin (`Arena/CheckerBase.lean`); a candidate to move down. -/
theorem checkProjRule_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (pty : EIdx) (ptyP : Expr) (cvj : IConstantVal) (cvjP : ConstantVal)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nF i : Nat)
    (hptyf : ptyP.hasFvar = false) (hCf : cvjP.type.hasFvar = false) :
    CSpec μ env fe
      (fun st => denoteE st pty = some ptyP ∧ Frontend.denoteCV st cvj = some cvjP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.checkProjRule μ fe pty cvj lps nP nF i)
      (fun st r => ∃ F rhsAP, ConLeche.checkProjRule (ConLeche.fueledOps μ F) env ptyP
          cvjP lpsP nP nF i = .ok rhsAP ∧ denoteE st r = some rhsAP) := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hp, hcv, hlps⟩ := hpre
  have hknot := hk.knot env fe henv
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  have hC := denoteCV_type hcv
  simp only [Arena.checkProjRule] at hrun
  -- the field's bound variable
  obtain ⟨bv, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hbv⟩ := internBVarE_run hck.state k1
  have c1 := p1.toCore hck
  -- the raw rule
  obtain ⟨orhs, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨h21, h22, h23, h24, h25, h26, h27⟩ := AM.of_run (P := fun t => t = s₁) rfl k2
    (ExprOps.pisToLams_spec (nP + nF) s₁ cvj.type bv p1.ok
      (by rw [denote_ext hC p1.ext]; rfl) (by rw [hbv]; rfl))
  have c2 := c1.trans ((PStep.of_caches h21 h22 h23 h25 h26).toCore c1.ok)
  have hraw := h27 _ _ (denote_ext hC p1.ext) hbv
  rcases orhs with _ | rhs
  · exact absurd z2 (AM.Never.fail _ _ _ _)
  obtain ⟨rhsP, hrawP, hrhs⟩ := denoteEO_some_inv hraw
  -- its scoping
  obtain ⟨b1, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨h31, h32, h33, hb1⟩ := AM.of_run (P := fun u => u = s₂) rfl k3
    (ExprOps.hasFvarFast_spec Arena.coreWalkFuel s₂ rhs c2.ok.state (by rw [hrhs]; rfl))
  have c3 := c2.trans (CoreStep.of_readonly c2.ok h31 h32 h33)
  have hrhs3 : denoteE s₃.store rhs = some rhsP := by rw [h31]; exact hrhs
  obtain ⟨b2, s₄, k4, z4⟩ := bindOk z3
  obtain ⟨h41, h42, h43, hb2⟩ := AM.of_run (P := fun u => u = s₃) rfl k4
    (ExprOps.looseBVarsBoundedFast_spec Arena.coreWalkFuel 0 s₃ rhs c3.ok.state
      (by rw [hrhs3]; rfl))
  have c4 := c3.trans (CoreStep.of_readonly c3.ok h41 h42 h43)
  have hrhs4 : denoteE s₄.store rhs = some rhsP := by rw [h41]; exact hrhs3
  obtain ⟨hg1, z5⟩ := AM.dunless_ok hnever z4
  replace z5 := AM.pure_bind_ok z5
  rw [hb1 rhsP hrhs, hb2 rhsP hrhs3] at hg1
  have hrf : rhsP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hg1
    exact hg1.1
  have hwsR : Expr.WScoped 0 rhsP := Expr.WScoped.of_not_hasFvar hrf
  -- annotated
  obtain ⟨rhsA, s₅, k5, z6⟩ := bindOk z5
  obtain ⟨ok5, x5, p5, ⟨rhsAP, hrhsA, hwsA, F₁, hF₁⟩⟩ := AM.of_run (P := fun u => u = s₄)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s₄.store u.store ∧
      u.pins = s₄.pins ∧ Core.SimE (ConLeche.annotateCore μ env) 0 rhsP u.store r)
    rfl k5 (hknot.annotate s₄ 0 rhs rhsP c4.ok hrhs4 hwsR)
  have c5 := c4.trans ⟨ok5, x5, p5⟩
  -- its four guards
  obtain ⟨b3, s₆, k6, z7⟩ := bindOk z6
  obtain ⟨h61, h62, h63, hb3⟩ := allLevelParamsDefined_run c5.ok.state
    (denoteNListE_ext c5.ext _ _ hlps) hrhsA k6
  have c6 := c5.trans (CoreStep.of_readonly c5.ok h61 h62 h63)
  have hA6 : denoteE s₆.store rhsA = some rhsAP := by rw [h61]; exact hrhsA
  obtain ⟨b4, s₇, k7, z8⟩ := bindOk z7
  obtain ⟨h71, h72, h73, hb4⟩ := constsResolveFFast_run c6.ok hA6 k7
  have c7 := c6.trans (CoreStep.of_readonly c6.ok h71 h72 h73)
  have hA7 : denoteE s₇.store rhsA = some rhsAP := by rw [h71]; exact hA6
  obtain ⟨b5, s₈, k8, z9⟩ := bindOk z8
  obtain ⟨h81, h82, h83, hb5⟩ := AM.of_run (P := fun u => u = s₇) rfl k8
    (ExprOps.looseBVarsBoundedFast_spec Arena.coreWalkFuel 0 s₇ rhsA c7.ok.state
      (by rw [hA7]; rfl))
  have c8 := c7.trans (CoreStep.of_readonly c7.ok h81 h82 h83)
  have hA8 : denoteE s₈.store rhsA = some rhsAP := by rw [h81]; exact hA7
  obtain ⟨b6, s₉, k9, z10⟩ := bindOk z9
  obtain ⟨h91, h92, h93, hb6⟩ := AM.of_run (P := fun u => u = s₈) rfl k9
    (ExprOps.hasFvarFast_spec Arena.coreWalkFuel s₈ rhsA c8.ok.state (by rw [hA8]; rfl))
  have c9 := c8.trans (CoreStep.of_readonly c8.ok h91 h92 h93)
  have hA9 : denoteE s₉.store rhsA = some rhsAP := by rw [h91]; exact hA8
  obtain ⟨hg2, z11⟩ := AM.dunless_ok hnever z10
  replace z11 := AM.pure_bind_ok z11
  rw [hb3, hb4, hb5 rhsAP hA7, hb6 rhsAP hA8] at hg2
  have hAf : rhsAP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hg2
    exact hg2.2
  -- the λ-telescope
  obtain ⟨ol, s₁₀, k10, z12⟩ := bindOk z11
  obtain ⟨hs10, hol⟩ := stripLams_pstep c9.ok.state hA9 k10
  subst s₁₀
  rcases ol with _ | ⟨rbinders, rrbody⟩
  · exact absurd z12 (AM.Never.fail _ _ _ _)
  obtain ⟨rbP, rrbP, hlamP, hrb, hrr⟩ := denoteBP_someB' hol
  have x1_4 : Ext s₁.store s₄.store := by rw [h41, h31]; exact h22
  have x1_9 : Ext s₁.store s₉.store := by rw [h91, h81, h71, h61]; exact x1_4.trans x5
  have hbv9 := denote_ext hbv x1_9
  obtain ⟨hg3, z13⟩ := AM.dunless_ok hnever z12
  replace z13 := AM.pure_bind_ok z13
  rw [beq_ehandle_eq c9.ok.state.wf hrr hbv9] at hg3
  -- the constructor's telescope
  have hC9 := denote_ext hC c9.ext
  obtain ⟨oc, s₁₁, k11, z14⟩ := bindOk z13
  obtain ⟨hs11, hoc⟩ := stripPis_pstep c9.ok.state hC9 k11
  subst s₁₁
  rcases oc with _ | ⟨cbindersR, cbody⟩
  · exact absurd z14 (AM.Never.fail _ _ _ _)
  obtain ⟨cbP, cbodyP, hpiP, hcb, -⟩ := denoteBP_someB' hoc
  obtain ⟨hg4, z15⟩ := AM.dunless_ok hnever z14
  replace z15 := AM.pure_bind_ok z15
  rw [domsMatchAux_eq c9.ok.state.wf hrb hcb] at hg4
  -- the projection type's parameters, opened
  have hp9 := denote_ext hp c9.ext
  obtain ⟨o1, s₁₂, k12, z16⟩ := bindOk z15
  obtain ⟨q12, ho1⟩ := openPisAtFvarsF_run c9.ok.state hp9 k12
  have c12 := c9.trans (q12.toCore c9.ok)
  rcases o1 with _ | ⟨fvsP, rest0⟩
  · exact absurd z16 (AM.Never.fail _ _ _ _)
  obtain ⟨vo1, rest0P, hopenP, hfvs, -⟩ := denoteOpen_some_inv ho1
  -- the constructor's parameter domains, instantiated
  have hC12 := denote_ext hC c12.ext
  obtain ⟨o2, s₁₃, k13, z17⟩ := bindOk z16
  obtain ⟨h131, h132, h133, h134, h135, h136⟩ := AM.of_run (P := fun u => u = s₁₂) rfl k13
    (ExprOps.instPisAtF_spec (instListSpec _) s₁₂ fvsP cvj.type c12.ok.state
      (by rw [hC12]; rfl) (by rw [hfvs]; rfl))
  have c13 := c12.trans ((PStep.of_caches h131 h132 h133 h134 h135).toCore c12.ok)
  have hi2 := h136 _ _ hC12 hfvs
  simp only [ConLeche.instPisAtF_eq] at hi2
  rcases o2 with _ | ⟨cdomsP, crestP⟩
  · exact absurd z17 (AM.Never.fail _ _ _ _)
  obtain ⟨cdP, crestPP, hinstP, hcd, hcr⟩ := denoteEP_some_inv hi2
  -- the scoping of the first frame
  obtain ⟨hfvsW0, -⟩ := ConLeche.openPisAtFvars_WScoped nP ptyP 0 hopenP
    (Expr.WScoped.of_not_hasFvar hptyf)
  have hfvsW : ∀ x ∈ vo1, Expr.WScoped nP x := by
    intro x hx
    have h0 := hfvsW0 x hx
    rwa [Nat.zero_add] at h0
  obtain ⟨hcdW, hcrW⟩ := ConLeche.instPisAt_WScoped (d := nP) vo1 cvjP.type
    hinstP (Expr.WScoped.of_not_hasFvar hCf) hfvsW
  -- the first definitional pin
  obtain ⟨ts1, s₁₄, k14, z18⟩ := bindOk z17
  obtain ⟨hs14, hts1⟩ := fvarTypeDs_run c13.ok.state fvsP
    (denoteEList_ext h132 _ _ hfvs) k14
  subst s₁₄
  obtain ⟨u1, s₁₅, k15, z19⟩ := bindOk z18
  obtain ⟨c15, F₂, hF₂⟩ := checkDefEqList_bridge hk henv (nP + nF) ts1 cdomsP _ _ s₁₃ s₁₅
    c13.ok hts1 hcd
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact ConLeche.fvarTypeD_WScoped ((hfvsW x hx).mono (by omega)))
    (fun b hb => (hcdW b hb).mono (by omega)) k15
  have c15' := c13.trans c15
  -- the fields, opened
  have hcr15 := denote_ext hcr c15.ext
  obtain ⟨o3, s₁₆, k16, z20⟩ := bindOk z19
  obtain ⟨q16, ho3⟩ := openPisAtFvarsF_run c15'.ok.state hcr15 k16
  have c16 := c15'.trans (q16.toCore c15'.ok)
  rcases o3 with _ | ⟨xFvs, crest2⟩
  · exact absurd z20 (AM.Never.fail _ _ _ _)
  obtain ⟨vx, crest2P, hopenX, hxfvs, -⟩ := denoteOpen_some_inv ho3
  -- the rule's λ-domains, instantiated
  have hspine16 : Frontend.denoteEList s₁₆.store (fvsP ++ xFvs) = some (vo1 ++ vx) :=
    Core.denoteEList_appendI
      (denoteEList_ext (h132.trans (c15.ext.trans q16.ext)) _ _ hfvs) hxfvs
  have hA16 := denote_ext hA9 (q12.ext.trans (h132.trans (c15.ext.trans q16.ext)))
  obtain ⟨o4, s₁₇, k17, z21⟩ := bindOk z20
  obtain ⟨h171, h172, h173, h174, h175, h176⟩ := AM.of_run (P := fun u => u = s₁₆) rfl k17
    (ExprOps.instLamsAtF_spec (instListSpec _) s₁₆ (fvsP ++ xFvs) rhsA c16.ok.state
      (by rw [hA16]; rfl) (by rw [hspine16]; rfl))
  have c17 := c16.trans ((PStep.of_caches h171 h172 h173 h174 h175).toCore c16.ok)
  have hi4 := h176 _ _ hA16 hspine16
  simp only [ConLeche.instLamsAtF_eq] at hi4
  rcases o4 with _ | ⟨ldoms, lrest⟩
  · exact absurd z21 (AM.Never.fail _ _ _ _)
  obtain ⟨ldP, lrestP, hlinstP, hld, -⟩ := denoteEP_some_inv hi4
  -- the scoping of the second frame
  obtain ⟨hxW, -⟩ := ConLeche.openPisAtFvars_WScoped nF crestPP nP hopenX hcrW
  have hspineW : ∀ a ∈ vo1 ++ vx, Expr.WScoped (nP + nF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsW a ha).mono (by omega)
    · exact hxW a ha
  obtain ⟨hldW, -⟩ := ConLeche.instLamsAt_WScoped (vo1 ++ vx) rhsAP hlinstP
    (Expr.WScoped.of_not_hasFvar hAf) hspineW
  -- the second definitional pin
  obtain ⟨ts2, s₁₈, k18, z22⟩ := bindOk z21
  obtain ⟨hs18, hts2⟩ := fvarTypeDs_run c17.ok.state (fvsP ++ xFvs)
    (denoteEList_ext h172 _ _ hspine16) k18
  subst s₁₈
  obtain ⟨u2, s₁₉, k19, z23⟩ := bindOk z22
  obtain ⟨c19, F₃, hF₃⟩ := checkDefEqList_bridge hk henv (nP + nF) ts2 ldoms _ _ s₁₇ s₁₉
    c17.ok hts2 hld
    (fun a ha => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      exact ConLeche.fvarTypeD_WScoped (hspineW x hx))
    (fun b hb => hldW b hb) k19
  have c19' := c17.trans c19
  -- the rule's type, inferred
  have hA19 := denote_ext hA16 (h172.trans c19.ext)
  obtain ⟨rty, s₂₀, k20, z24⟩ := bindOk z23
  obtain ⟨ok20, x20, p20, ⟨rtyP, -, -, F₄, hF₄⟩⟩ := AM.of_run (P := fun u => u = s₁₉)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s₁₉.store u.store ∧
      u.pins = s₁₉.pins ∧ Core.SimE (ConLeche.inferTypeCore μ env) 0 rhsAP u.store r)
    rfl k20 (hknot.infer s₁₉ 0 rhsA rhsAP c19'.ok hA19 hwsA)
  have c20 := c19'.trans ⟨ok20, x20, p20⟩
  obtain ⟨rfl, rfl⟩ := pureOk z24
  refine ⟨c20, max (max F₁ F₂) (max F₃ F₄), rhsAP, ?_, denote_ext hA19 x20⟩
  -- the pure side
  have g1 : (ConLeche.fueledOps μ (max (max F₁ F₂) (max F₃ F₄))).annotate env 0 rhsP
      = .ok rhsAP := ConLeche.annotateCore_mono (by omega) hF₁
  have g4 : (ConLeche.fueledOps μ (max (max F₁ F₂) (max F₃ F₄))).inferType env 0 rhsAP
      = .ok rtyP := ConLeche.inferTypeCore_mono (by omega) hF₄
  have g2 := checkDefEqList_mono (F' := max (max F₁ F₂) (max F₃ F₄)) (by omega) hF₂
  have g3 := checkDefEqList_mono (F' := max (max F₁ F₂) (max F₃ F₄)) (by omega) hF₃
  simp only [ConLeche.checkProjRule, hrawP]
  rw [if_pos hg1]
  simp only [bind, Except.bind, g1]
  rw [if_pos hg2]
  simp only [hlamP]
  rw [if_pos hg3]
  simp only [hpiP]
  rw [if_pos hg4]
  simp only [hopenP, hinstP, g2, hopenX, hlinstP, g3, g4, pure, Except.pure]

/-! ## `projFnRule` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:909-921 projFnRule — **the
stored rule of an installed projection function**, in run form: the firing
mode off `recRulePlain`, the recursor name off `projFnName`, and the two
rescue bits stamped by `recRuleBits` at the index `fe` (read through its
index spec at the store, so the caches may serve another index). -/
theorem projFnRule_run {μ : CheckMode} {env envC : Env} {fe feC : IFEnv}
    {s s' : AState} {T ctorName : NIdx} {pty rhsA : EIdx} {TP ctorNameP : ConLeche.Name}
    {ptyP rhsAP : Expr} {nP nF i : Nat} {rl : IRecRule}
    (hok : CheckOK μ envC feC s) (hi : IFEnvOKS env fe s.store)
    (hT : denoteN s.store.ns T = some TP) (hC : denoteN s.store.ns ctorName = some ctorNameP)
    (hp : denoteE s.store pty = some ptyP) (hA : denoteE s.store rhsA = some rhsAP)
    (hrun : Arena.projFnRule fe T ctorName pty nP nF i rhsA s = .ok (rl, s')) :
    CoreStep μ envC feC s s' ∧ Frontend.denoteRule s'.store rl =
      some (ConLeche.projFnRule env.find? TP ctorNameP ptyP nP nF i rhsAP) := by
  simp only [Arena.projFnRule] at hrun
  obtain ⟨b, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := AM.of_run (P := fun t => t = s) rfl k1
    (ExprOps.recRulePlain_spec Arena.coreWalkFuel s pty nP nP nP hok.state (by rw [hp]; rfl))
  have c1 := (PStep.of_caches h1 h2 h3 h5 h6).toCore hok
  have hb : b = Expr.recRulePlain ptyP nP nP nP := h7 ptyP hp
  obtain ⟨nm, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hnm⟩ := projFnName_run c1.ok.state (denoteN_ext hT c1.ext) k2
  have c2 := c1.trans (p2.toCore c1.ok)
  have hrl : Frontend.denoteRule s₂.store
      (⟨ctorName, nF, nP, (if b then .plain else .inert), rhsA, false, false, false⟩ :
        IRecRule) =
      some (⟨ctorNameP, nF, nP,
        (if Expr.recRulePlain ptyP nP nP nP then .plain else .inert),
        rhsAP, false, false, false⟩ : RecRule) := by
    subst hb
    cases Expr.recRulePlain ptyP nP nP nP <;>
      simp [Frontend.denoteRule, Frontend.denoteFire, denoteN_ext hC c2.ext,
        denote_ext hA c2.ext]
  obtain ⟨hfr, hrl'⟩ := recRuleBits_runX c2.ok (hi.mono c2.ext s₂ rfl) hnm hrl z2
  exact ⟨c2.trans ⟨Core.CheckOK.ofReadbackFrame c2.ok hfr, hfr.ext, hfr.pins⟩, hrl'⟩

/-! ## `eqHeadLevel` -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:213-220 eqHeadLevel — the level
an equality head carries, in run form: read-only, and `.zero` off shape (the
twin's `zeroLevel` is the pinned `.zero`). -/
theorem eqHeadLevel_run {s s' : AState} {h : EIdx} {hP : Expr} {u : LIdx}
    (hok : StateOK s) (hp : PinsOK s) (hd : denoteE s.store h = some hP)
    (hrun : Arena.eqHeadLevel h s = .ok (u, s')) :
    s' = s ∧ denoteL s.store.ls u = some (ConLeche.eqHeadLevel hP) := by
  simp only [Arena.eqHeadLevel] at hrun
  obtain ⟨v, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hv⟩ := view_run k1
  subst s₁
  cases v
  case const n us =>
    obtain ⟨nm, ls, rfl, -, hls⟩ := denote_const_inv hok.wf hv hd
    obtain ⟨w, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨hs2, hw⟩ := viewLs_run k2
    subst s₂
    have hll := denoteLs_of_view hw hls
    have hlen := denoteLList_length _ _ hll
    rcases w with _ | ⟨l, _ | ⟨l', rest⟩⟩
    · obtain ⟨h1, h2⟩ := zeroLevel_run hp z2
      refine ⟨h1, ?_⟩
      rcases ls with _ | ⟨x, _ | ⟨y, ys⟩⟩
      · exact h2
      · simp at hlen
      · simp at hlen
    · obtain ⟨rfl, hs'⟩ := pureOk z2
      subst s'
      simp only [denoteLList, opt2] at hll
      cases hl : denoteL s.store.ls u with
      | none => rw [hl] at hll; simp at hll
      | some x =>
        rw [hl] at hll
        simp only [Option.some.injEq] at hll
        subst hll
        exact ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := zeroLevel_run hp z2
      refine ⟨h1, ?_⟩
      rcases ls with _ | ⟨x, _ | ⟨y, ys⟩⟩
      · exact h2
      · simp at hlen
      · exact h2
  all_goals
    obtain ⟨h1, h2⟩ := zeroLevel_run hp z1
    refine ⟨h1, ?_⟩
    have hz : ConLeche.eqHeadLevel hP = .zero := by
      cases hP with
      | const n ls =>
        rw [denoteE_view_eq hok.wf hv] at hd
        simp [denoteEView] at hd
      | _ => rfl
    rw [hz]; exact h2

/-- con-leche: none — a handle list read at an index with a FALLBACK handle:
the pure list at the same index with the fallback's denotation.  The iota
certificates read the equation's three arguments this way (`targs.getD k b0`
against con-leche's `targs.getD k (.bvar 0)`). -/
theorem denoteEList_getD_fb {st : EStore} {b : EIdx} {bP : Expr}
    (hb : denoteE st b = some bP) :
    ∀ {hs : List EIdx} {xs : List Expr}, Frontend.denoteEList st hs = some xs →
      ∀ (k : Nat), denoteE st (hs.getD k b) = some (xs.getD k bP) := by
  intro hs
  induction hs with
  | nil =>
    intro xs h k
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simpa using hb
  | cons a as ih =>
    intro xs h k
    obtain ⟨x, xs', hx, hxs', rfl⟩ := denoteEList_cons h
    cases k with
    | zero => simpa using hx
    | succ k => simpa using ih hxs' k

/-! ## Two shape tests, and a guard fold -/

/-- con-leche: none — a handle whose view is not a `.forallE` does not denote
one.  The pure matcher's catch-all arm, read off the arena's. -/
theorem denote_not_forallE {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {e : Expr} (hw : st.view h = some v) (he : denoteE st h = some e)
    (hv : ∀ ty b m, v ≠ .forallE ty b m) : ∀ a b m, e ≠ .forallE a b m := by
  intro a b m hae
  subst hae
  rw [denoteE_view_eq hwf hw] at he
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff]

/-- con-leche: none — **`List.allM` of a core-grade Boolean test over a
denoting handle list**: the answer is the pure `all` over the denotations. -/
theorem allM_E_cstep {μ : CheckMode} {env : Env} {fe : IFEnv} {f : EIdx → AM Bool}
    {g : Expr → Bool} (Q : EStore → Prop)
    (hQx : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (hf : ∀ (a : EIdx) (aP : Expr) (s₀ s' : AState) (b : Bool), CheckOK μ env fe s₀ →
      Q s₀.store → denoteE s₀.store a = some aP → f a s₀ = .ok (b, s') →
      CoreStep μ env fe s₀ s' ∧ b = g aP) :
    ∀ (ps : List EIdx) (psP : List Expr) (s₀ s' : AState) (b : Bool),
      CheckOK μ env fe s₀ → Q s₀.store → Frontend.denoteEList s₀.store ps = some psP →
      ps.allM f s₀ = .ok (b, s') → CoreStep μ env fe s₀ s' ∧ b = psP.all g := by
  intro ps
  induction ps with
  | nil =>
    intro psP s₀ s' b hok _ h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.allM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | cons a as ih =>
    intro psP s₀ s' b hok hQ h hrun
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteEList_cons h
    simp only [List.allM] at hrun
    obtain ⟨c, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hc⟩ := hf a x s₀ s1 c hok hQ hx k1
    cases c with
    | false =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      simp only [List.all_cons, ← hc, Bool.false_and]
    | true =>
      obtain ⟨p2, hb⟩ := ih xs s1 s' b p1.ok (hQx p1.ext hQ)
        (denoteEList_ext p1.ext _ _ hxs) z1
      refine ⟨p1.trans p2, ?_⟩
      simp only [List.all_cons, ← hc, Bool.true_and, hb]

end ConRon.Bridge.Inductives
