/-
# `ConRon.Bridge.Inductives.BlockInstall` — Theorem 1 for the uniform install's stages

`Arena/Inductives/BlockInstall.lean`'s twins against
`ConLeche/Kernel/Inductives/BlockInstall.lean` (task #105), whose `…F` index
twins (`BlockInstallF.lean`) the twin collapses (its module note, deviation 1):
the formers' stage (telescopes, the two agreements, the cons), the
constructors' stage, the positivity check on the stored constructors, the
index sorts and the constructors' cons.  The capability record and official's
`is_rec` are `Bridge/Inductives/Install.lean`'s.

**Grades.**  Every stage that calls the knot is `CSpecF` against con-leche's
function at `fueledOpsM .verified` — the template is upstream's cached bridge
(`ConLeche/Verify/Cached/BlockRunC.lean`, `NestPosC.lean`), and every statement
carries exactly the scoping facts those carry.  The two conses are pure on both
sides (`EnvRel`, `InstRel`).

**The formers' stage runs its knot calls at the ENTRY index** and conses the
formers only after the last of them, so `checkBlockInds_spec` is `CSpecF` at
`env fe`: `CheckOK false env fe` still holds at the end.  Its answer carries the
new index answering for `env₁` (`EnvRel`), which is what the caller's flush
needs (`ReadOK.flush`) to get `CheckOK false env₁ fe₁`.
-/
module

import ConRon.Bridge.Inductives.SumInstall
import ConRon.Bridge.Inductives.Install
import ConRon.Bridge.Inductives.BlockShape
public import ConRon.Bridge.Inductives.Positivity
import ConLeche.Verify.Cached.BlockRunC
import ConLeche.Verify.BridgeWfImp
-- `Verify.openPisAtFvars_length`, which no public import re-exports
import ConLeche.Verify.Denote.IndFrame
/- `simp only` unfolds the toolchain's monadic list functions (`List.filterM`,
`List.findM?`, …), whose bodies `Init.Data.List.Control` does not expose. -/
import all Init.Data.List.Control
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Inductives.StructParts
import ConLeche.Verify.Cached.NestPosC
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

namespace BI

/-! ## Small helpers -/

/-- con-leche: none — a checked former with its result sort. -/
def dCvL (st : EStore) (x : IConstantVal × LIdx) : Option (ConstantVal × Level) := do
  let c ← Frontend.denoteCV st x.1
  let l ← denoteL st.ls x.2
  pure (c, l)

theorem dCvL_ext : DExt dCvL := by
  intro st st' hx x y h
  simp only [dCvL] at h ⊢
  cases h1 : Frontend.denoteCV st x.1 with
  | none => rw [h1] at h; exact nomatch h
  | some c =>
  cases h2 : denoteL st.ls x.2 with
  | none => rw [h1, h2] at h; exact nomatch h
  | some l =>
  rw [h1, h2] at h
  rw [denoteCV_ext h1 hx, denoteL_ext h2 hx]
  exact h

theorem dCvL_inv {st : EStore} {x : IConstantVal × LIdx} {y : ConstantVal × Level}
    (h : dCvL st x = some y) :
    Frontend.denoteCV st x.1 = some y.1 ∧ denoteL st.ls x.2 = some y.2 := by
  simp only [dCvL] at h
  cases h1 : Frontend.denoteCV st x.1 with
  | none => rw [h1] at h; exact nomatch h
  | some c =>
  cases h2 : denoteL st.ls x.2 with
  | none => rw [h1, h2] at h; exact nomatch h
  | some l =>
  rw [h1, h2] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl⟩

/-- con-leche: none — a store-preserving read is a `CoreStep`
(`Bridge/Checker/DivMod.lean`'s `CoreStep.of_store`, which this tier cannot
import). -/
theorem coreStep_of_store {env : Env} {fe : IFEnv} {s s' : AState}
    (hck : CheckOK false env fe s) (h1 : s'.store = s.store) (h2 : s'.caches = s.caches)
    (h3 : s'.pins = s.pins) : CoreStep env fe s s' :=
  ⟨hck.mono ⟨by rw [h1]; exact hck.state.wf⟩ (by rw [h1]; exact Ext.refl _) h2 h3,
    by rw [h1]; exact Ext.refl _, h3⟩

end BI

open BI

/-! ## Stage 1: the formers -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:106-117 checkBlockTele
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:27-36 checkBlockTeleF
One member's type former, against `checkBlockTele (fueledOpsM .verified)`; the
stored type is closed (`checkBlockTeleS_sim`'s answer). -/
theorem checkBlockTele_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (nP : Nat) (ms : Arena.MemberShape) (msP : ConLeche.MemberShape) :
    CSpecF env fe
      (fun st => dMember st ms = some msP)
      (Arena.checkBlockTele .verified fe nP ms)
      (fun st r v => Frontend.denoteCV st r.1 = some v.1 ∧ denoteL st.ls r.2 = some v.2 ∧
        Expr.WScoped 0 v.1.type)
      (ConLeche.checkBlockTele (fueledOpsM .verified) env nP msP) := by
  intro s₀ s' r hok hm hrun
  obtain ⟨cv, dv, nI, cs⟩ := msP
  obtain ⟨hcv, rfl, -, -⟩ := dMember_inv hm
  dsimp only at hcv
  simp only [Arena.checkBlockTele] at hrun
  obtain ⟨_, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨c1, F₁, hF₁⟩ := checkConstantVal_bridge hk hok henv hcv k1
  have hcA := denoteCV_ext hcv c1.ext
  have hw1 : Expr.WScoped 0 cv.type :=
    Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  have fk1 : FOk (ConLeche.checkConstantVal (fueledOpsM .verified) env cv) () :=
    ⟨F₁, by rw [checkConstantVal_datF]; exact hF₁⟩
  obtain ⟨t2, s₂, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨c2, ⟨cvTaP, sP⟩, ⟨h2a, h2b, hw2⟩, fk2⟩ := checkSumTele_specF (env := env) fe
    (nP + ms.nIdx) ms.cvT cv hw1 s₁ s₂ t2 c1.ok hcA k2
  obtain ⟨cvTa, sI⟩ := t2
  dsimp only at h2a h2b hw2 z2
  obtain ⟨sq, s₃, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨rfl, hsq⟩ := stripPis_pstep c2.ok.state (denoteCV_type h2a) k3
  cases sq with
  | none => exact absurd z3 (fun h => AM.fail_ok h)
  | some q =>
  obtain ⟨bs, body⟩ := q
  obtain ⟨xs, x, hxs, -, hbody⟩ := denoteBP_some hsq
  dsimp only at z3
  obtain ⟨srt, s₄, k4, z4⟩ := AM.bind_ok z3
  obtain ⟨p4, hsrt⟩ := internSortE_run c2.ok.state h2b k4
  have hbeq := beq_of_denoteE p4.ok.wf (denote_ext hbody p4.ext) hsrt
  by_cases hb : (body == srt) = true
  · rw [ite_eq_left hb] at z4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
    have c4 := c1.trans (c2.trans (p4.toCore c2.ok))
    refine ⟨c4, (cvTaP, sP), ⟨denoteCV_ext h2a p4.ext, denoteL_ext h2b p4.ext, hw2⟩, ?_⟩
    rw [hb] at hbeq
    unfold ConLeche.checkBlockTele
    refine FOk.bind fk1 (FOk.bind fk2 ?_)
    simp only [hxs]
    refine FOk.bind FOk.unwrapOr ?_
    exact FOk.ite_pos (by simpa using hbeq.symm) (FOk.pure _)
  · rw [ite_eq_right hb] at z4
    exact absurd z4 (fun h => AM.fail_ok h)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:119-126 checkBlockTeles
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:38-45 checkBlockTelesF
The members' type formers, in block order; every stored type closed
(`checkBlockTelesS_sim`). -/
theorem checkBlockTeles_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (nP : Nat) :
    ∀ (mss : List Arena.MemberShape) (mssP : List ConLeche.MemberShape),
    CSpecF env fe
      (fun st => mss.mapM (dMember st) = some mssP)
      (Arena.checkBlockTeles .verified fe nP mss)
      (fun st r v => r.mapM (dCvL st) = some v ∧ ∀ x ∈ v, Expr.WScoped 0 x.1.type)
      (ConLeche.checkBlockTeles (fueledOpsM .verified) env nP mssP) := by
  intro mss
  induction mss with
  | nil =>
    intro mssP s₀ s' r hok hms hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.checkBlockTeles] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, [], ⟨rfl, fun _ h => nomatch h⟩, FOk.pure _⟩
  | cons ms rest ih =>
    intro mssP s₀ s' r hok hms hrun
    obtain ⟨msP, restP, rfl, hm, hrest⟩ := mapM_option_cons_inv hms
    simp only [Arena.checkBlockTeles] at hrun
    obtain ⟨t1, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, v1, ⟨h1a, h1b, hw1⟩, fk1⟩ := checkBlockTele_specF fe hk henv nP ms msP
      s₀ s₁ t1 hok hm k1
    obtain ⟨t2, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨c2, v2, ⟨h2, hw2⟩, fk2⟩ := ih restP s₁ s₂ t2 c1.ok
      (dMember_ext.list c1.ext _ _ hrest) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨c1.trans c2, v1 :: v2, ⟨?_, ?_⟩, ?_⟩
    · refine mapM_option_cons ?_ h2
      simp only [dCvL, denoteCV_ext h1a c2.ext, denoteL_ext h1b c2.ext]
      rfl
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hw1
      · exact hw2 x hx
    · unfold ConLeche.checkBlockTeles
      exact FOk.bind fk1 (FOk.bind fk2 (FOk.pure _))

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:128-142 checkBlockDomsAt
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:47-56 checkBlockDomsAtF
**The parameter-domain agreement's comparison**, against
`checkBlockDomsAt (fueledOpsM .verified)`, the scoping hypotheses split as
`checkBlockDomsAtS_sim`'s (`hc` for the opened variables' annotations, `ht`
for the expected domains). -/
theorem checkBlockDomsAt_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) (off : Nat)
    (fvs doms : List EIdx) (fvsP domsP : List Expr)
    (hc : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → Expr.WScoped (off + i) x.fvarTypeD)
    (ht : ∀ (i : Nat) (x : Expr), domsP[i]? = some x → Expr.WScoped (off + i) x) :
    ∀ (j : Nat),
    CSpecF env fe
      (fun st => Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st doms = some domsP)
      (Arena.checkBlockDomsAt .verified fe off fvs doms j) (fun _ _ _ => True)
      (ConLeche.checkBlockDomsAt (fueledOpsM .verified) env off fvsP domsP j) := by
  have hknot := hk.knot env fe henv
  intro j
  induction j with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.checkBlockDomsAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, FOk.pure ()⟩
  | succ j ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hfvs, hdoms⟩ := hpre
    simp only [Arena.checkBlockDomsAt] at hrun
    obtain ⟨a, s1, k1, hz1⟩ := AM.bind_ok hrun
    obtain ⟨ha, hs1⟩ := unwrapOr_ok k1
    subst s1
    obtain ⟨b, s2, k2, hz2⟩ := AM.bind_ok hz1
    obtain ⟨hb, hs2⟩ := unwrapOr_ok k2
    subst s2
    obtain ⟨aP, haP, hda⟩ := ExprOps.denoteEList_getElem? fvs fvsP hfvs j a ha
    obtain ⟨bP, hbP, hdb⟩ := ExprOps.denoteEList_getElem? doms domsP hdoms j b hb
    obtain ⟨t, s3, k3, hz3⟩ := AM.bind_ok hz2
    obtain ⟨hs3, ht3⟩ := fvarTypeD_run hok.state hda k3
    subst s3
    obtain ⟨c, s4, k4, hz4⟩ := AM.bind_ok hz3
    obtain ⟨hok4, hx4, hp4, hsim⟩ := AM.of_run (P := fun u => u = s₀)
      (Q := fun r u => CheckOK false env fe u ∧ Ext s₀.store u.store ∧
        u.pins = s₀.pins ∧
        Core.SimV (ConLeche.isDefEqCore .verified false env) (off + j) aP.fvarTypeD bP r)
      rfl k4 (hknot.defeq s₀ (off + j) t b aP.fvarTypeD bP hok ht3 hdb (hc j aP haP)
        (ht j bP hbP))
    have fkd := FOk.isDefEq hsim
    obtain ⟨hcv, hz5⟩ := AM.dunless_ok AM.Never.fail_any hz4
    replace hz5 := AM.pure_bind_ok hz5
    subst hcv
    obtain ⟨hstep, u, -, fk⟩ := ih s4 s' r hok4
      ⟨denoteEList_ext hx4 _ _ hfvs, denoteEList_ext hx4 _ _ hdoms⟩ hz5
    refine ⟨⟨hstep.ok, hx4.trans hstep.ext, by rw [hstep.pins, hp4]⟩, (), trivial, ?_⟩
    unfold ConLeche.checkBlockDomsAt
    simp only [haP, hbP]
    refine FOk.bind FOk.unwrapOr (FOk.bind FOk.unwrapOr (FOk.bind fkd ?_))
    simpa using fk

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:144-164 checkBlockAgree
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:58-73 checkBlockAgreeF
**Official's two agreements between the members**, against
`checkBlockAgree (fueledOpsM .verified)`, at closed stored types
(`checkBlockAgreeS_sim`'s `h0`/`hcvs`).  The sort comparison is `lvlEq?`,
the cached `Level.isEquiv`. -/
theorem checkBlockAgree_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) (nP : Nat)
    (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal) (s0 : LIdx) (s0P : Level)
    (h0 : Expr.WScoped 0 cvTa₀P.type) :
    ∀ (cvs : List (IConstantVal × LIdx)) (cvsP : List (ConstantVal × Level)),
    (∀ x ∈ cvsP, Expr.WScoped 0 x.1.type) →
    CSpecF env fe
      (fun st => Frontend.denoteCV st cvTa₀ = some cvTa₀P ∧ denoteL st.ls s0 = some s0P ∧
        cvs.mapM (dCvL st) = some cvsP)
      (Arena.checkBlockAgree .verified fe nP cvTa₀ s0 cvs) (fun _ _ _ => True)
      (ConLeche.checkBlockAgree (fueledOpsM .verified) env nP cvTa₀P s0P cvsP) := by
  intro cvs
  induction cvs with
  | nil =>
    intro cvsP _ s₀ s' r hok hpre hrun
    obtain ⟨-, -, hcvs⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
    subst hcvs
    simp only [Arena.checkBlockAgree] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, FOk.pure ()⟩
  | cons x rest ih =>
    intro cvsP hws s₀ s' r hok hpre hrun
    obtain ⟨h0d, hs0, hcvs⟩ := hpre
    obtain ⟨xP, restP, rfl, hx, hrest⟩ := mapM_option_cons_inv hcvs
    obtain ⟨hxcv, hxs⟩ := dCvL_inv hx
    obtain ⟨cvTa, s⟩ := x
    obtain ⟨cvTaP, sP⟩ := xP
    dsimp only at hxcv hxs
    have hwx : Expr.WScoped 0 cvTaP.type := hws _ List.mem_cons_self
    simp only [Arena.checkBlockAgree] at hrun
    -- tq₀
    obtain ⟨o0, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, ho0⟩ := openPisAtFvarsF_run hok.state (denoteCV_type h0d) k1
    obtain ⟨tq0, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨rfl, rfl⟩ := unwrapOr_ok k2
    obtain ⟨fvs0, b0⟩ := tq0
    obtain ⟨xs0, x0, hq0, hxs0, -⟩ := denoteOpen_some_inv ho0
    -- tq
    obtain ⟨o1, s₃, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨p3, ho1⟩ := openPisAtFvarsF_run p1.ok (denote_ext (denoteCV_type hxcv) p1.ext) k3
    obtain ⟨tq, s₄, k4, z4⟩ := AM.bind_ok z3
    obtain ⟨rfl, rfl⟩ := unwrapOr_ok k4
    obtain ⟨fvs1, b1⟩ := tq
    obtain ⟨xs1, x1, hq1, hxs1, -⟩ := denoteOpen_some_inv ho1
    have hxs0' := denoteEList_ext p3.ext _ _ hxs0
    have hl0 := denoteEList_length hxs0'
    have hl1 := denoteEList_length hxs1
    dsimp only at z4
    by_cases hlen : (fvs1.length == fvs0.length) = true
    · rw [ite_eq_left hlen] at z4
      replace z4 := AM.pure_bind_ok z4
      obtain ⟨doms, s₅, k5, z5⟩ := AM.bind_ok z4
      obtain ⟨p5, hdoms⟩ := fvarTypeDs_run fvs0 xs0 p3.ok hxs0' k5
      have c5 := (p1.trans (p3.trans p5)).toCore hok
      obtain ⟨u6, s₆, k6, z6⟩ := AM.bind_ok z5
      obtain ⟨c6, u6v, -, fk6⟩ := checkBlockDomsAt_specF fe hk henv 0 fvs1 doms xs1
        (xs0.map Expr.fvarTypeD) (ConRon.Bridge.Inductives.openers_typeD_WScoped hq1 hwx)
        (fun i y hy => by
          rw [List.getElem?_map] at hy
          obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hy
          exact ConRon.Bridge.Inductives.openers_typeD_WScoped hq0 h0 i z hz) nP s₅ s₆ u6 c5.ok
        ⟨denoteEList_ext p5.ext _ _ hxs1, hdoms⟩ k6
      have c16 := c5.trans c6
      obtain ⟨o7, s₇, k7, z7⟩ := AM.bind_ok z6
      obtain ⟨c7, ho7⟩ := lvlEq?_crun c6.ok (denoteL_ext hxs c16.ext)
        (denoteL_ext hs0 c16.ext) k7
      obtain ⟨b8, s₈, k8, z8⟩ := AM.bind_ok z7
      obtain ⟨hb8, rfl⟩ := liftFueled_ok k8
      obtain ⟨hcv, hz9⟩ := AM.dunless_ok AM.Never.fail_any z8
      replace hz9 := AM.pure_bind_ok hz9
      subst hcv
      have c17 := c16.trans c7
      obtain ⟨c9, u9, -, fk9⟩ := ih restP (fun y hy => hws y (List.mem_cons_of_mem _ hy)) s₈ s'
        r c7.ok ⟨denoteCV_ext h0d c17.ext, denoteL_ext hs0 c17.ext,
          dCvL_ext.list c17.ext _ _ hrest⟩ hz9
      refine ⟨c17.trans c9, (), trivial, ?_⟩
      unfold ConLeche.checkBlockAgree
      rw [ho7] at hb8
      simp only [hq0, hq1, hb8]
      refine FOk.bind FOk.unwrapOr (FOk.bind FOk.unwrapOr ?_)
      refine FOk.ite_pos (by rw [← hl0, ← hl1]; simpa using hlen)
        (FOk.bind fk6 (FOk.bind FOk.liftFueled ?_))
      exact FOk.ite_pos rfl fk9
    · rw [ite_eq_right hlen] at z4
      exact absurd z4 (AM.Never.fail_any _ _ _)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:166-170 consBlockInds
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:75-80 consBlockIndsF
**The formers consed**, each with its capability record (`blockCapsAt`, pure
on both sides): the index pushes answer for con-leche's conses
(`EnvRel.push`, each). -/
theorem consBlockInds_rel {st : EStore} (hwf : StoreWF st)
    {p₁ : Arena.BlockShape} {p₁P : ConLeche.BlockShape} (hp : dShape st p₁ = some p₁P)
    (isRec : Bool) :
    ∀ (cvs : List IConstantVal) (cvsP : List ConstantVal) (i : Nat) (fe : IFEnv) (env : Env),
      cvs.mapM (Frontend.denoteCV st) = some cvsP → EnvRel env fe st →
      EnvRel (ConLeche.consBlockInds p₁P isRec cvsP i env)
        (Arena.consBlockInds p₁ isRec cvs i fe) st
  | [], cvsP, i, fe, env, hcvs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
    subst hcvs
    exact h
  | cv :: rest, cvsP, i, fe, env, hcvs, h => by
    obtain ⟨cvP, restP, rfl, hcv, hrest⟩ := mapM_option_cons_inv hcvs
    have hci : Frontend.denoteCI st (.indInfo cv (Arena.blockCapsAt p₁ i isRec)) =
        some (.indInfo cvP (ConLeche.blockCapsAt p₁P i isRec)) := by
      simp only [Frontend.denoteCI, hcv, blockCapsAt_denote hp]
    simp only [Arena.consBlockInds, ConLeche.consBlockInds]
    exact consBlockInds_rel hwf hp isRec rest restP (i + 1) _ _ hrest (h.push hwf hci)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:172-185 checkBlockInds
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:82-93 checkBlockIndsF
**Stage 1**, against `checkBlockInds (fueledOpsM .verified)`: the k formers
checked and agreed at the ENTRY index (so `CheckOK false env fe` still holds at
the end — the frame is `CoreStep`), then consed as declared.  The answer: the
new index answers for con-leche's `env₁` (`EnvRel`), and the completed shape
denotes con-leche's. -/
theorem checkBlockInds_spec {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (isRec : Bool) :
    CSpecF env fe
      (fun st => dShape st p = some pP ∧ EnvRel env fe st)
      (Arena.checkBlockInds .verified fe p isRec)
      (fun st r v => EnvRel v.1 r.1 st ∧ dShape st r.2 = some v.2)
      (ConLeche.checkBlockInds (fueledOpsM .verified) env pP isRec) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hp, hfe⟩ := hpre
  obtain ⟨ms, rs, nP, el, sP, lg, ip⟩ := pP
  obtain ⟨hms, hrs, rfl, hel, hsP, rfl, rfl⟩ := dShape_inv hp
  dsimp only at hms hrs hel hsP
  simp only [Arena.checkBlockInds] at hrun
  cases hmem : p.members with
  | nil =>
    rw [hmem] at hrun
    exact absurd hrun (fun h => AM.fail_ok h)
  | cons ms₀ rest =>
  rw [hmem] at hrun hms
  obtain ⟨ms₀P, restP, rfl, hm0, hrestP⟩ := mapM_option_cons_inv hms
  dsimp only at hrun
  obtain ⟨t1, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨c1, ⟨cvTa₀P, s0P⟩, ⟨h1a, h1b, hw1⟩, fk1⟩ := checkBlockTele_specF fe hk henv
    p.nP ms₀ ms₀P s₀ s₁ t1 hok hm0 k1
  obtain ⟨cvTa₀, s0⟩ := t1
  dsimp only at h1a h1b z1
  obtain ⟨cvs, s₂, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨c2, cvsP, ⟨h2, hw2⟩, fk2⟩ := checkBlockTeles_specF fe hk henv p.nP rest
    restP s₁ s₂ cvs c1.ok (dMember_ext.list c1.ext _ _ hrestP) k2
  have x12 := c2.ext
  obtain ⟨u3, s₃, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨c3, u3v, -, fk3⟩ := checkBlockAgree_specF fe hk henv p.nP cvTa₀ cvTa₀P s0 s0P
    hw1 cvs cvsP hw2 s₂ s₃ u3 c2.ok
    ⟨denoteCV_ext h1a x12, denoteL_ext h1b x12, h2⟩ k3
  have c13 := c1.trans (c2.trans c3)
  obtain ⟨p₁, s₄, k4, z4⟩ := AM.bind_ok z3
  obtain ⟨c4, hp₁⟩ := BlockShape.withSort_spec fe p
    ⟨ms₀P :: restP, rs, p.nP, el, sP, p.large, p.isProp⟩ s0 s0P s₃ s₄ p₁
    c3.ok ⟨dShape_ext c13.ext _ _ hp, denoteL_ext h1b (c2.ext.trans c3.ext)⟩ k4
  have c14 := c13.trans c4
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
  refine ⟨c14, (ConLeche.consBlockInds (ConLeche.BlockShape.withSort
      ⟨ms₀P :: restP, rs, p.nP, el, sP, p.large, p.isProp⟩ s0P) isRec
      ((ms₀P :: restP).map (·.declared)) 0 env,
      ConLeche.BlockShape.withSort ⟨ms₀P :: restP, rs, p.nP, el, sP, p.large, p.isProp⟩ s0P),
    ⟨?_, hp₁⟩, ?_⟩
  · have hdecl : ((ms₀ :: rest).map (·.declared)).mapM (Frontend.denoteCV s'.store) =
        some ((ms₀P :: restP).map (·.declared)) := by
      exact declared_denote (dMember_ext.list c14.ext _ _ (mapM_option_cons hm0 hrestP))
    exact consBlockInds_rel c14.ok.state.wf hp₁ isRec _ _ 0 fe env hdecl
      (hfe.mono c14.ext)
  · unfold ConLeche.checkBlockInds
    exact FOk.bind fk1 (FOk.bind fk2 (FOk.bind fk3 (FOk.pure _)))

/-! ## Stage 1b: the constructors, and the positivity check -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:191-197 BlockShape.nestCtx
**The block's positivity context** at the canonical variables `fvs`, denoted
at any lookup `find?` (the twin's lookup is the `fe` its readers take). -/
theorem BlockShape.nestCtx_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (fvs : List EIdx) (fvsP : List Expr) (find? : ConLeche.Name → Option ConstantInfo) :
    PSpec (fun st => dShape st p = some pP ∧ Frontend.denoteEList st fvs = some fvsP)
      (Arena.BlockShape.nestCtx p fvs)
      (fun st r => dCtx st find? r = some (pP.nestCtx fvsP find?)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hp, hfvs⟩ := hpre
  have hnames := BlockShape.memberNames_spec hp
  have hlps := BlockShape.lps_spec hp
  have hnI := BlockShape.nIdxs_spec hp
  have hform : p.formers.mapM (Frontend.denoteCV s₀.store) = some pP.formers := by
    obtain ⟨hms, -⟩ := dShape_inv hp
    simp only [Arena.BlockShape.formers, ConLeche.BlockShape.formers]
    clear hrun hnI
    generalize pP.members = ys at hms ⊢
    generalize p.members = xs at hms
    induction xs generalizing ys with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
      subst hms; rfl
    | cons x xs ih =>
      obtain ⟨y, ys', rfl, hy, hys⟩ := mapM_option_cons_inv hms
      exact mapM_option_cons (dMember_inv hy).1 (ih ys' hys)
  obtain ⟨ms, rs, nP, el, sP, lg, ip⟩ := pP
  obtain ⟨-, -, rfl, -, hsP, rfl, rfl⟩ := dShape_inv hp
  dsimp only at hsP
  simp only [Arena.BlockShape.nestCtx] at hrun
  obtain ⟨lv, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, hlv⟩ := paramLevels_spec p.lps _ s₀ s₁ lv hok hlps k1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
  refine ⟨p1, ?_⟩
  have x := p1.ext
  simp only [dCtx, denoteNListE_ext x _ _ hnames, denoteNListE_ext x _ _ hlps,
    denoteEList_ext x _ _ hfvs, denoteL_ext hsP x, hlv, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, ite_true, ConLeche.BlockShape.nestCtx, hnI,
    dExt_denoteCV.list x _ _ hform]
  rfl

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:198-207 checkBlockCtors
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:97-106 checkBlockCtorsF
**The constructors of every member**, each against its member's former at its
telescope, against `checkBlockCtors (fueledOpsM .verified) env₀ env pP`.  The
formers' types are closed (`checkBlockCtorsS_sim`'s `hl`). -/
theorem checkBlockCtors_specF {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (env₀ : Env) :
    ∀ (mss : List Arena.MemberShape) (mssP : List ConLeche.MemberShape),
    (∀ ms ∈ mssP, Expr.WScoped 0 ms.cvT.type) →
    CSpecF env fe
      (fun st => dShape st p = some pP ∧ mss.mapM (dMember st) = some mssP ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkBlockCtors .verified fe₀ fe p mss)
      (fun _ _ _ => True)
      (ConLeche.checkBlockCtors (fueledOpsM .verified) env₀ env pP mssP) := by
  intro mss
  induction mss with
  | nil =>
    intro mssP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hms, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.checkBlockCtors] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, by
      simp only [ConLeche.checkBlockCtors]; exact FOk.pure _⟩
  | cons ms rest ih =>
    intro mssP hws s₀ s' r hok hpre hrun
    obtain ⟨hp, hms, hok₀⟩ := hpre
    obtain ⟨msP, restP, rfl, hm, hrest⟩ := mapM_option_cons_inv hms
    obtain ⟨cvT, dv, nI, csP⟩ := msP
    obtain ⟨hcvT, rfl, hcs, -⟩ := dMember_inv hm
    dsimp only at hcvT hcs
    have hlps := BlockShape.lps_spec hp
    obtain ⟨mm, rs, nP, el, sP, lg, ip⟩ := pP
    obtain ⟨-, -, rfl, -, hsP, rfl, rfl⟩ := dShape_inv hp
    dsimp only at hsP
    simp only [Arena.checkBlockCtors] at hrun
    obtain ⟨t1, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, _, _, fk1⟩ := checkSumCtors_specF fe₀ fe hk henv
      ms.cvT.name cvT.name p.lps _ p.nP ms.nIdx p.resSort sP p.isProp p.large ms.cvT cvT env₀
      ms.ctors csP (ConLeche.Cached.ws0_hasFvar (hws _ List.mem_cons_self)) s₀ s₁ t1 hok
      ⟨denoteCV_name hcvT, hlps, hsP, hcvT, by rw [← dCtors_eq_denoteCtors]; exact hcs,
        hok₀⟩ k1
    have x1 := c1.ext
    obtain ⟨c2, _, _, fk2⟩ := ih restP
      (fun cv h => hws cv (List.mem_cons_of_mem _ h)) s₁ s' r c1.ok
      ⟨dShape_ext x1 _ _ hp, dMember_ext.list x1 _ _ hrest, hok₀.mono x1⟩ z1
    refine ⟨c1.trans c2, (), trivial, ?_⟩
    unfold ConLeche.checkBlockCtors
    exact FOk.bind fk1 fk2

/-- con-leche: ConLeche/Verify/Cached/BlockRunC.lean:387-395 checkBlockCtors_types
The constructors' stage passed only at closed constructor types — the fact the
positivity stage needs (`checkBlockPositivityS_sim`'s `hct`), off the pure run
`FOk` hands over. -/
theorem checkBlockCtors_types {μ : CheckMode} {env₀ env : Env} {q : ConLeche.BlockShape}
    {l : List ConLeche.MemberShape}
    (h : FOk (ConLeche.checkBlockCtors (fueledOpsM μ) env₀ env q l) ()) :
    ∀ ctorList ∈ l.map (·.ctors), ∀ c ∈ ctorList, Expr.WScoped 0 c.1.type := by
  obtain ⟨F, hF⟩ := h
  rw [checkBlockCtors_datF] at hF
  exact ConLeche.Cached.checkBlockCtors_types hF

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:228-250 checkAbsCtorSorts
**The fields' universes at the holes**, against
`checkAbsCtorSorts (fueledOpsM .verified) env ctxP`, pairwise to the shorter list.
The twin's `isProp` (read once by the caller) is con-leche's per-call
`Level.isEquiv ctxP.sort .zero == some true` (`hprop`); the normal forms are
scoped at the holes' depth (`checkAbsCtorSortsS_sim`'s `hos`). -/
theorem checkAbsCtorSorts_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) (isProp : Bool)
    (hprop : isProp = (Level.isEquiv ctxP.sort .zero == some true)) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
      (os : List (List Arena.NestFieldKind × EIdx)) (osP : List (List ConLeche.NestFieldKind × Expr)),
    (∀ o ∈ osP, Expr.WScoped (ctxP.hiAt 0) o.2) →
    CSpecF env fe
      (fun st => dCtx st ctxP.find? ctx = some ctxP ∧ dCtors st cs = some csP ∧
        os.mapM (dOut st) = some osP)
      (Arena.checkAbsCtorSorts .verified fe ctx isProp cs os) (fun _ _ _ => True)
      (ConLeche.checkAbsCtorSorts (fueledOpsM .verified) env ctxP csP osP) := by
  intro cs
  induction cs with
  | nil =>
    intro csP os osP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hcs, -⟩ := hpre
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.checkAbsCtorSorts] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, by
      simp only [ConLeche.checkAbsCtorSorts]; exact FOk.pure ()⟩
  | cons c cs ih =>
    intro csP os osP hws s₀ s' r hok hpre hrun
    obtain ⟨hctx, hcs, hos⟩ := hpre
    obtain ⟨cP, csP', rfl, hc, hcs'⟩ := mapM_option_cons_inv hcs
    cases os with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hos
      subst hos
      simp only [Arena.checkAbsCtorSorts] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, (), trivial, by
        simp only [ConLeche.checkAbsCtorSorts]; exact FOk.pure ()⟩
    | cons o os =>
    obtain ⟨oP, osP', rfl, ho, hos'⟩ := mapM_option_cons_inv hos
    obtain ⟨cv, hcv, rfl⟩ : ∃ cv, Frontend.denoteCV s₀.store c.1 = some cv ∧ cP = (cv, c.2) := by
      simp only [dCtor, Option.map_eq_some_iff] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨x, hx, rfl⟩
    obtain ⟨tyN, htyN, rfl⟩ : ∃ tyN, denoteE s₀.store o.2 = some tyN ∧ oP = (o.1.map kindOf, tyN) := by
      simp only [dOut, Option.map_eq_some_iff] at ho
      obtain ⟨x, hx, rfl⟩ := ho
      exact ⟨x, hx, rfl⟩
    have hW : Expr.WScoped (ctxP.hiAt 0) tyN := hws _ List.mem_cons_self
    obtain ⟨namesP, lpsP, paramsP, sortP, _, hceq, hn, hl, -, hsort, -, _⟩ := dCtx_inv hctx
    have hl' : Frontend.denoteNList s₀.store.ns ctx.lps = some ctxP.lps := by rw [hceq]; exact hl
    have hsort' : denoteL s₀.store.ls ctx.sort = some ctxP.sort := by rw [hceq]; exact hsort
    have hhi : ctx.hiAt 0 = ctxP.hiAt 0 := by
      rw [hceq]
      simp [Arena.NestCtx.hiAt, ConLeche.NestCtx.hiAt, denoteNList_length _ _ hn]
    simp only [Arena.checkAbsCtorSorts] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨h1s, h1c, h1p, hb⟩ := allLevelParamsDefined_run hok.state hl' htyN k1
    have c1 := coreStep_of_store hok h1s h1c h1p
    obtain ⟨hbt, z2⟩ := AM.dunless_ok AM.Never.fail_any z1
    replace z2 := AM.pure_bind_ok z2
    obtain ⟨oq, s₂, k2, z3⟩ := AM.bind_ok z2
    obtain ⟨p2, hoq⟩ := openPisAtFvarsF_run c1.ok.state
      (denote_ext htyN c1.ext) k2
    obtain ⟨xq, s₃, k3, z4⟩ := AM.bind_ok z3
    obtain ⟨rfl, hs3⟩ := unwrapOr_ok k3
    subst s₃
    obtain ⟨fvs, rest⟩ := xq
    obtain ⟨xsP, xP, hxq, hxs, -⟩ := denoteOpen_some_inv hoq
    rw [hhi] at hxq
    have c2 := c1.trans (p2.toCore c1.ok)
    obtain ⟨u5, s₅, k5, z5⟩ := AM.bind_ok z4
    have hfvsc := ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hW
    obtain ⟨c5, u5v, -, fk5⟩ := checkStructFieldSortsI_specF fe hk henv isProp false ctx.sort
      ctxP.sort (ctx.hiAt 0) fvs [] xsP [] c.2 (by rw [hhi]; exact hfvsc) s₂ s₅ u5 c2.ok
      ⟨denoteL_ext hsort' c2.ext, hxs, rfl⟩ k5
    have c25 := c2.trans c5
    obtain ⟨c6, u6, -, fk6⟩ := ih csP' os osP' (fun y hy => hws y (List.mem_cons_of_mem _ hy))
      s₅ s' r c5.ok ⟨dCtx_ext _ c25.ext _ _ hctx, dCtors_ext c25.ext _ _ hcs',
        dOut_ext.list c25.ext _ _ hos'⟩ z5
    refine ⟨c25.trans c6, (), trivial, ?_⟩
    rw [hb] at hbt
    unfold ConLeche.checkAbsCtorSorts
    simp only [hxq]
    refine FOk.ite_pos hbt (FOk.bind FOk.unwrapOr ?_)
    rw [← hprop, ← hhi]
    exact FOk.bind fk5 fk6

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:252-258 checkAbsCtorSortsAll
`checkAbsCtorSorts` on every member's constructors (`checkAbsCtorSortsAllS_sim`). -/
theorem checkAbsCtorSortsAll_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) (isProp : Bool)
    (hprop : isProp = (Level.isEquiv ctxP.sort .zero == some true)) :
    ∀ (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat)))
      (oss : List (List (List Arena.NestFieldKind × EIdx)))
      (ossP : List (List (List ConLeche.NestFieldKind × Expr))),
    (∀ os ∈ ossP, ∀ o ∈ os, Expr.WScoped (ctxP.hiAt 0) o.2) →
    CSpecF env fe
      (fun st => dCtx st ctxP.find? ctx = some ctxP ∧ css.mapM (dCtors st) = some cssP ∧
        dOutss st oss = some ossP)
      (Arena.checkAbsCtorSortsAll .verified fe ctx isProp css oss) (fun _ _ _ => True)
      (ConLeche.checkAbsCtorSortsAll (fueledOpsM .verified) env ctxP cssP ossP) := by
  intro css
  induction css with
  | nil =>
    intro cssP oss ossP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hcs, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.checkAbsCtorSortsAll] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, by
      simp only [ConLeche.checkAbsCtorSortsAll]; exact FOk.pure ()⟩
  | cons cs css ih =>
    intro cssP oss ossP hws s₀ s' r hok hpre hrun
    obtain ⟨hctx, hcss, hoss⟩ := hpre
    simp only [dOutss] at hoss
    obtain ⟨csP, cssP', rfl, hc, hcss'⟩ := mapM_option_cons_inv hcss
    cases oss with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hoss
      subst hoss
      simp only [Arena.checkAbsCtorSortsAll] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, (), trivial, by
        simp only [ConLeche.checkAbsCtorSortsAll]; exact FOk.pure ()⟩
    | cons os oss =>
    obtain ⟨osP, ossP', rfl, ho, hoss'⟩ := mapM_option_cons_inv hoss
    simp only [Arena.checkAbsCtorSortsAll] at hrun
    obtain ⟨u1, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, u1v, -, fk1⟩ := checkAbsCtorSorts_specF fe hk henv ctx ctxP isProp hprop cs csP
      os osP (hws osP List.mem_cons_self) s₀ s₁ u1 hok ⟨hctx, hc, ho⟩ k1
    have x1 := c1.ext
    obtain ⟨c2, u2, -, fk2⟩ := ih cssP' oss ossP' (fun y hy => hws y (List.mem_cons_of_mem _ hy))
      s₁ s' r c1.ok ⟨dCtx_ext _ x1 _ _ hctx, dCtors_ext.list x1 _ _ hcss',
        dOutss_ext x1 _ _ hoss'⟩ z1
    refine ⟨c1.trans c2, (), trivial, ?_⟩
    unfold ConLeche.checkAbsCtorSortsAll
    exact FOk.bind fk1 fk2

/-! ## Stage 2: the tail -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:298-305 checkBlockIdxSorts
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:108-120 checkBlockIdxSortsF
Every member's INDEX binders have sorts, each member at its former's
telescope, against `checkBlockIdxSorts (fueledOpsM .verified) env pP`.  The
formers' types are closed (`checkBlockIdxSortsS_sim`'s `hl`). -/
theorem checkBlockIdxSorts_specF {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) :
    ∀ (mss : List Arena.MemberShape) (mssP : List ConLeche.MemberShape),
    (∀ ms ∈ mssP, Expr.WScoped 0 ms.cvT.type) →
    CSpecF env fe
      (fun st => dShape st p = some pP ∧ mss.mapM (dMember st) = some mssP)
      (Arena.checkBlockIdxSorts .verified fe p mss)
      (fun _ _ _ => True)
      (ConLeche.checkBlockIdxSorts (fueledOpsM .verified) env pP mssP) := by
  intro mss
  induction mss with
  | nil =>
    intro mssP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hms⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.checkBlockIdxSorts] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨CoreStep.refl hok, (), trivial, by
      simp only [ConLeche.checkBlockIdxSorts]; exact FOk.pure _⟩
  | cons ms rest ih =>
    intro mssP hws s₀ s' r hok hpre hrun
    obtain ⟨hp, hms⟩ := hpre
    obtain ⟨msP, restP, rfl, hm, hrest⟩ := mapM_option_cons_inv hms
    obtain ⟨cvT, dv, nI, csP⟩ := msP
    obtain ⟨hcv, rfl, -, -⟩ := dMember_inv hm
    obtain ⟨mm, rs, nP, el, sP, lg, ip⟩ := pP
    obtain ⟨-, -, rfl, -, hsP, rfl, rfl⟩ := dShape_inv hp
    dsimp only at hsP hcv
    have hw : Expr.WScoped 0 cvT.type := hws _ List.mem_cons_self
    simp only [Arena.checkBlockIdxSorts] at hrun
    obtain ⟨oq, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hoq⟩ := openPisAtFvarsF_run hok.state (denoteCV_type hcv) k1
    obtain ⟨tq, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨rfl, hs2⟩ := unwrapOr_ok k2
    subst s₂
    obtain ⟨fvs, b⟩ := tq
    obtain ⟨xsP, xP, htq, hxs, -⟩ := denoteOpen_some_inv hoq
    have c1 := p1.toCore hok
    obtain ⟨is, s₃, k3, z3⟩ := AM.bind_ok z2
    have hxPos : ∀ (i : Nat) (x : Expr), (xsP.drop p.nP)[i]? = some x →
        Expr.WScoped (p.nP + i) x.fvarTypeD := by
      intro i x hx
      rw [List.getElem?_drop] at hx
      have := ConRon.Bridge.Inductives.openers_typeD_WScoped htq hw (p.nP + i) x hx
      simpa using this
    obtain ⟨c3, _, _, fk3⟩ := checkStructFieldSortsI_specF fe hk henv true false p.resSort sP
      p.nP (fvs.drop p.nP) [] (xsP.drop p.nP) [] ms.nIdx hxPos s₁ s₃ is c1.ok
      ⟨denoteL_ext hsP c1.ext, denoteEList_drop hxs p.nP, rfl⟩ k3
    have c13 := c1.trans c3
    obtain ⟨c4, _, _, fk4⟩ := ih restP (fun cv h => hws cv (List.mem_cons_of_mem _ h))
      s₃ s' r c3.ok ⟨dShape_ext c13.ext _ _ hp, dMember_ext.list c13.ext _ _ hrest⟩ z3
    refine ⟨c13.trans c4, (), trivial, ?_⟩
    unfold ConLeche.checkBlockIdxSorts
    simp only [htq]
    exact FOk.bind FOk.unwrapOr (FOk.bind fk3 fk4)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:309-312 consBlockCtors
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:122-125 consBlockCtorsF
**The members' constructors consed**, member by member.  PURE on both sides:
`InstRel` over `consSumCtors_spec`. -/
theorem consBlockCtors_spec {st : EStore} (hwf : StoreWF st) (nP : Nat) :
    ∀ (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat)))
      (fe : IFEnv) (env : Env), css.mapM (dCtors st) = some cssP → EnvRel env fe st →
      InstRel (fun e => e = ConLeche.consBlockCtors nP cssP env) st
        (Arena.consBlockCtors nP css fe)
  | [], cssP, fe, env, hcss, hfe => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcss
    subst hcss
    exact ⟨env, hfe, rfl⟩
  | cs :: css, cssP, fe, env, hcss, hfe => by
    obtain ⟨csP, cssP', rfl, hcs, hcss'⟩ := mapM_option_cons_inv hcss
    rw [dCtors_eq_denoteCtors] at hcs
    obtain ⟨e1, he1, rfl⟩ := (consSumCtors_spec st nP cs csP fe env hwf hcs hfe).denote
    exact consBlockCtors_spec hwf nP css cssP' _ _ hcss' he1

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:260-274 blockNestCtx
**The walk's context** of a block, against
`blockNestCtx (m := FueledM) pP cvsP env.find?`, the lookup the environment
(the index's spec, `nestHoles_spec`), with the scoping facts
`blockNestCtxS_sim` states of it: the context's stored constants closed, the
holes variables scoped at the holes' depth, the canonical variables scoped
there and one per parameter. -/
theorem blockNestCtx_spec {env : Env} (fe : IFEnv) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (hT : ∀ cv ∈ pP.formers, Expr.WScoped 0 cv.type) :
    CSpecF env fe
      (fun st => dShape st p = some pP)
      (Arena.blockNestCtx p)
      (fun st r v => dCtx st env.find? r.1 = some v.1 ∧ Frontend.denoteEList st r.2 = some v.2 ∧
        NestCtxOk v.1 ∧ (∀ x ∈ v.2, Expr.WScoped (v.1.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty) ∧
        (∀ x ∈ v.1.params, Expr.WScoped (v.1.hiAt 0) x) ∧ v.1.params.length = v.1.nP ∧
        ConLeche.nestHoles v.1 = some v.2 ∧ v.1.nP = pP.nP)
      (ConLeche.blockNestCtx (m := FueledM) pP env.find?) := by
  intro s₀ s' r hok hp hrun
  have hcvs : p.formers.mapM (Frontend.denoteCV s₀.store) = some pP.formers := by
    obtain ⟨hms, -⟩ := dShape_inv hp
    simp only [Arena.BlockShape.formers, ConLeche.BlockShape.formers]
    clear hrun
    generalize pP.members = ys at hms ⊢
    generalize p.members = xs at hms
    induction xs generalizing ys with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
      subst hms; rfl
    | cons x xs ih =>
      obtain ⟨y, ys', rfl, hy, hys⟩ := mapM_option_cons_inv hms
      exact mapM_option_cons (dMember_inv hy).1 (ih ys' hys)
  simp only [Arena.blockNestCtx] at hrun
  generalize hfm : p.formers = cvs at hrun hcvs
  generalize hfP : pP.formers = cvsP at hcvs hT
  cases cvs with
  | nil => exact absurd hrun (fun h => AM.fail_ok h)
  | cons cv0 rest =>
  obtain ⟨cv0P, restP, rfl, hcv0, -⟩ := mapM_option_cons_inv hcvs
  have hnP : p.nP = pP.nP := (dShape_inv hp).2.2.1
  dsimp only at hrun
  obtain ⟨o, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, ho⟩ := openPisAtFvarsF_run hok.state (denoteCV_type hcv0) k1
  obtain ⟨pq, s₂, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨rfl, hs2⟩ := unwrapOr_ok k2
  subst s₂
  obtain ⟨fvs, b⟩ := pq
  obtain ⟨xs, x, hpq, hxs, -⟩ := denoteOpen_some_inv ho
  rw [hnP] at hpq
  obtain ⟨ctx, s₃, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨p3, hctx⟩ := BlockShape.nestCtx_spec p pP fvs xs env.find? s₁ s₃ ctx p1.ok
    ⟨dShape_ext p1.ext _ _ hp, hxs⟩ k3
  have p13 := p1.trans p3
  obtain ⟨oh, s₄, k4, z4⟩ := AM.bind_ok z3
  obtain ⟨p4, hoh⟩ := nestHoles_spec (env := env) ctx _ s₃ s₄ oh p13.ok hctx k4
  obtain ⟨holes, s₅, k5, z5⟩ := AM.bind_ok z4
  obtain ⟨rfl, hs5⟩ := unwrapOr_ok k5
  subst s₅
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z5
  obtain ⟨holesP, hnh, hholes⟩ := hoh
  have hw0 : Expr.WScoped 0 cv0P.type := hT _ List.mem_cons_self
  have hctxOk : NestCtxOk (pP.nestCtx xs env.find?) :=
    ⟨fun n ci hf => (henv.consts ci (Env.find?_mem hf)).1, fun cv hcv => by
      have : cv ∈ pP.formers := by
        simpa [ConLeche.BlockShape.nestCtx, ConLeche.BlockShape.formers] using hcv
      rw [hfP] at this
      exact ConLeche.Cached.ws0_hasFvar (hT cv this)⟩
  have hparN : ∀ y ∈ xs, Expr.WScoped pP.nP y := by
    intro y hy
    have := (ConLeche.openPisAtFvars_WScoped pP.nP cv0P.type 0 hpq hw0).1 y hy
    rwa [Nat.zero_add] at this
  have hpar : ∀ y ∈ xs, Expr.WScoped ((pP.nestCtx xs env.find?).hiAt 0) y := fun y hy =>
    Expr.WScoped.mono (by simp [ConLeche.NestCtx.hiAt, ConLeche.BlockShape.nestCtx])
      (hparN y hy)
  refine ⟨(p13.trans p4).toCore hok, (pP.nestCtx xs env.find?, holesP),
    ⟨dCtx_ext _ p4.ext _ _ hctx, hholes, hctxOk, ConLeche.nestHoles_ok hctxOk hparN hnh, hpar,
      ConLeche.Verify.openPisAtFvars_length _ hpq, hnh, rfl⟩, ?_⟩
  unfold ConLeche.blockNestCtx
  simp only [hfP, List.head?_cons]
  refine FOk.bind FOk.unwrapOr ?_
  simp only [hpq]
  refine FOk.bind FOk.unwrapOr ?_
  simp only [hnh]
  exact FOk.bind FOk.unwrapOr (FOk.pure _)

/-- con-leche: none — the members' constructor lists, denoted. -/
theorem memberCtors_denote {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (hp : dShape st p = some pP) : p.memberCtors.mapM (dCtors st) = some pP.memberCtors := by
  obtain ⟨hms, -⟩ := dShape_inv hp
  simp only [Arena.BlockShape.memberCtors, ConLeche.BlockShape.memberCtors]
  generalize pP.members = ys at hms ⊢
  generalize p.members = xs at hms
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms; rfl
  | cons x xs ih =>
    obtain ⟨y, ys', rfl, hy, hys⟩ := mapM_option_cons_inv hms
    exact mapM_option_cons (dMember_inv hy).2.2.1 (ih ys' hys)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:276-291 checkBlockPositivity
**The block's positivity, on its stored constructors**, against
`checkBlockPositivity (fueledOpsM .verified) env env.find? pP` (the twin's
lookup is the environment `fe`): the walk's context (`blockNestCtx_spec`), the
uniform-occurrence check (`nestUniform_spec`), the root frame
(`nestRoot_spec`), the fields' universes (`checkAbsCtorSortsAll`, the twin's
`isProp` read once through `lvlEq?`).  The formers' and the constructors'
types are closed (`checkBlockPositivityS_sim`'s `hT`, `hct`). -/
theorem checkBlockPositivity_spec {env : Env} (fe : IFEnv)
    (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (hT : ∀ cv ∈ pP.formers, Expr.WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ pP.memberCtors, ∀ c ∈ ctorsA, Expr.WScoped 0 c.1.type) :
    CSpecF env fe
      (fun st => dShape st p = some pP)
      (Arena.checkBlockPositivity .verified fe p)
      (fun st r v => dOutss st r.1 = some v.1 ∧ dState st r.2 = some v.2)
      (ConLeche.checkBlockPositivity (fueledOpsM .verified) env env.find? pP) := by
  intro s₀ s' r hok hp hrun
  have hcas := memberCtors_denote hp
  have hcl : ∀ cs ∈ pP.memberCtors, ∀ c ∈ cs, c.1.type.hasFvar = false :=
    fun cs hcs c hc => ConLeche.Cached.ws0_hasFvar (hct cs hcs c hc)
  simp only [Arena.checkBlockPositivity] at hrun
  obtain ⟨t1, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨c1, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, -, hnh, -⟩, fk1⟩ :=
    blockNestCtx_spec fe henv p pP hT s₀ s₁ t1 hok hp k1
  obtain ⟨ctx, holes⟩ := t1
  dsimp only at hctx hholes hhw hpar hnh z1
  have x1 := c1.ext
  obtain ⟨u2, s₂, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨c2, u2v, -, fk2⟩ := nestUniform_spec env.find? ctx ctxP p.memberCtors pP.memberCtors
    s₁ s₂ u2 c1.ok ⟨hctx, dCtors_ext.list x1 _ _ hcas⟩ k2
  have x12 := c1.ext.trans c2.ext
  obtain ⟨t3, s₃, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨c3, ⟨outsP, nsP⟩, ⟨houts, hns, hwN⟩, fk3⟩ := nestRoot_spec hk henv hctxOk holes holesP
    (fun y hy => (hhw y hy).1) (by rw [ConLeche.nestHoles_length hnh]; exact Nat.le_refl _) hpar
    p.memberCtors pP.memberCtors {} {} [] [] hcl s₂ s₃ t3 c2.ok
    ⟨dCtx_ext _ c2.ext _ _ hctx, denoteEList_ext c2.ext _ _ hholes,
      dCtors_ext.list x12 _ _ hcas, by simp [dState], rfl⟩ k3
  obtain ⟨outs, ns⟩ := t3
  simp only [List.nil_append] at houts
  dsimp only at houts hns z3
  have x13 := x12.trans c3.ext
  obtain ⟨z, s₄, k4, z4⟩ := AM.bind_ok z3
  obtain ⟨hs4, hz⟩ := zeroLevel_run c3.ok.pins k4
  subst s₄
  obtain ⟨ov, s₅, k5, z5⟩ := AM.bind_ok z4
  obtain ⟨namesP, lpsP, paramsP, sortP, _, hceq, -, -, -, hsort, -, _⟩ := dCtx_inv hctx
  have hfind : ctxP.find? = env.find? := by rw [hceq]
  have hsort' : denoteL s₃.store.ls ctx.sort = some ctxP.sort := by
    rw [hceq]; exact denoteL_ext hsort (c2.ext.trans c3.ext)
  obtain ⟨c5, hov⟩ := lvlEq?_crun c3.ok hsort' hz k5
  have x15 := x13.trans c5.ext
  obtain ⟨u6, s₆, k6, z6⟩ := AM.bind_ok z5
  obtain ⟨c6, u6v, -, fk6⟩ := checkAbsCtorSortsAll_specF fe hk henv ctx ctxP _ (by rw [hov])
    p.memberCtors pP.memberCtors outs outsP hwN s₅ s₆ u6 c5.ok
    ⟨by rw [hfind]; exact dCtx_ext _ ((c2.ext.trans c3.ext).trans c5.ext) _ _ hctx,
      dCtors_ext.list x15 _ _ hcas, dOutss_ext c5.ext _ _ houts⟩ k6
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z6
  refine ⟨(((c1.trans c2).trans c3).trans c5).trans c6, (outsP, nsP),
    ⟨dOutss_ext (c5.ext.trans c6.ext) _ _ houts, dState_ext (c5.ext.trans c6.ext) _ _ hns⟩, ?_⟩
  unfold ConLeche.checkBlockPositivity
  exact FOk.bind fk1 (FOk.bind fk2 (FOk.bind fk3 (FOk.bind fk6 (FOk.pure _))))

end ConRon.Bridge.Inductives
