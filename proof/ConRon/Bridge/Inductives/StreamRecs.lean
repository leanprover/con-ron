/-
# `ConRon.Bridge.Inductives.StreamRecs` — Theorem 1 for the stream's recursors

`Arena/Inductives/StreamRecs.lean` against con-leche's
`ConLeche/Kernel/Inductives/StreamRecs.lean`, function for function, in the
tier's run form (`CSpecF` for what calls the knot, `PStep` for what does not);
the upstream simulation this mirrors is `Verify/Cached/GenRecC.lean`'s
`recDomsAtS_spec` … `streamRecsCheckS_spec`.

Every comparison runs at one environment `env`, the generated install, whose
index `fe` the caller holds `CheckOK` at (`Bridge/Inductives/BlockTail.lean`);
the K flags (`streamKCheck_run`) read no environment.  Errors are related by kind only (DESIGN
§3.1) and a failing run owes nothing, so no message content appears here.
-/
module

public import ConRon.Bridge.Inductives.RecCheck
public import ConRon.Arena.Inductives.StreamRecs
public import ConLeche.Kernel.Inductives.StreamRecs
import ConLeche.Verify.Cached.BridgeCS3
import ConLeche.Verify.Inductives.StreamRecsInv
import ConLeche.Verify.Denote.IndFrame
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.ExprOps.Subst
import ConRon.Bridge.Specs
import ConRon.Bridge.Inductives.BlockShape

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

namespace SR

/-! ## The list relations -/

/-- con-leche: none — **a level-handle-list comparison is a structural
comparison**: `denoteLList` is injective (`denoteLList_inj`). -/
theorem beq_of_denoteLList {st : EStore} (hwf : StoreWF st) {as bs : List LIdx}
    {xs ys : List Level} (ha : denoteLList st.ls as = some xs)
    (hb : denoteLList st.ls bs = some ys) : (as == bs) = (xs == ys) := by
  obtain ⟨rk, hrk⟩ := hwf
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl
    rw [ha] at hb
    exact Option.some.inj hb
  · rintro rfl
    exact denoteLList_inj hrk.lsWF as bs xs ha hb

/-- con-leche: none — `denoteRules` at a cons, inverted. -/
theorem denoteRules_cons_inv {st : EStore} {r : IRecRule} {rs : List IRecRule}
    {ys : List RecRule} (h : Frontend.denoteRules st (r :: rs) = some ys) :
    ∃ y ys', ys = y :: ys' ∧ Frontend.denoteRule st r = some y ∧
      Frontend.denoteRules st rs = some ys' := by
  simp only [Frontend.denoteRules] at h
  cases h1 : Frontend.denoteRule st r with
  | none => rw [h1] at h; simp at h
  | some y =>
    cases h2 : Frontend.denoteRules st rs with
    | none => rw [h1, h2] at h; simp at h
    | some ys' =>
      rw [h1, h2] at h
      exact ⟨y, ys', (Option.some.inj h).symm, rfl, rfl⟩

/-- con-leche: none — `denoteRules` at the empty list, inverted. -/
theorem denoteRules_nil_inv {st : EStore} {ys : List RecRule}
    (h : Frontend.denoteRules st [] = some ys) : ys = [] := by
  simp only [Frontend.denoteRules, Option.some.injEq] at h; exact h.symm

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:111-128 streamNestedOk —
the pins lifted past the index binders, as the twin's `mapM`. -/
theorem liftList_run (n : Nat) : ∀ (ps : List EIdx) (psP : List Expr) (s₀ s' : AState)
    (r : List EIdx), StateOK s₀ → Frontend.denoteEList s₀.store ps = some psP →
    ps.mapM (liftLooseBVarsFast coreWalkFuel n 0) s₀ = .ok (r, s') →
    PStep s₀ s' ∧ Frontend.denoteEList s'.store r = some (psP.map (Expr.liftLooseBVars n 0)) := by
  intro ps
  induction ps with
  | nil =>
    intro psP s₀ s' r hok hd hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons p ps ih =>
    intro psP s₀ s' r hok hd hrun
    simp only [Frontend.denoteEList] at hd
    cases h1 : denoteE s₀.store p with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : Frontend.denoteEList s₀.store ps with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [List.mapM_cons] at hrun
    obtain ⟨y, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨st1, x1, -, c1, p1, -, -, hrel⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
      (ExprOps.liftLooseBVarsFast_spec coreWalkFuel n 0 s₀ p hok (by rw [h1]; rfl))
    have q1 : PStep s₀ s1 := PStep.of_caches st1 x1 c1 p1
    obtain ⟨ys, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨q2, hys⟩ := ih xs s1 s2 ys q1.ok (denoteEList_ext q1.ext _ _ h2) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨q1.trans q2, ?_⟩
    simp only [List.map_cons, Frontend.denoteEList,
      denote_ext (hrel x h1) q2.ext, hys]

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:111-128 streamNestedOk —
the index variables, as the twin's `mapM` over `List.range`. -/
theorem bvarList_run (n : Nat) : ∀ (l : List Nat) (s₀ s' : AState) (r : List EIdx),
    StateOK s₀ → l.mapM (fun i => internBVarE (n - 1 - i)) s₀ = .ok (r, s') →
    PStep s₀ s' ∧ Frontend.denoteEList s'.store r = some (l.map fun i => Expr.bvar (n - 1 - i)) := by
  intro l
  induction l with
  | nil =>
    intro s₀ s' r hok hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons i l ih =>
    intro s₀ s' r hok hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨y, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨q1, hy⟩ := internBVarE_run hok k1
    obtain ⟨ys, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨q2, hys⟩ := ih s1 s2 ys q1.ok k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨q1.trans q2, ?_⟩
    simp only [List.map_cons, Frontend.denoteEList, denote_ext hy q2.ext, hys]

/-- con-leche: none — `denoteOpen` survives the arena's growth. -/
theorem denoteOpen_ext {st st' : EStore} (hx : Ext st st') (o : Option (List EIdx × EIdx))
    (v : Option (List Expr × Expr)) (h : denoteOpen st o = some v) :
    denoteOpen st' o = some v := by
  cases o with
  | none => exact h
  | some q =>
    obtain ⟨fvs, e⟩ := q
    obtain ⟨xs, x, rfl, h1, h2⟩ := denoteOpen_some_inv h
    exact denoteOpen_some (denoteEList_ext hx _ _ h1) (denote_ext h2 hx)

end SR

open SR

/-! ## The closedness test -/

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:72-109 recTyCheck, ruleAgree —
the test both open with. -/
theorem streamClosed_run {s₀ s' : AState} {a b : EIdx} {x y : Expr} {r : Bool}
    (hok : StateOK s₀) (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hrun : Arena.streamClosed a b s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r = (x.looseBVarsBounded 0 && !x.hasFvar && !y.hasFvar) := by
  simp only [Arena.streamClosed] at hrun
  obtain ⟨b1, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, rfl⟩ := RC.looseBVarsBoundedFast_pstep hok hx k1
  split at z1
  · rename_i h1
    obtain ⟨b2, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, rfl⟩ := RC.hasFvarFast_pstep p1.ok (denote_ext hx p1.ext) k2
    split at z2
    · rename_i h2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
      exact ⟨p1.trans p2, by simp [h1, h2]⟩
    · rename_i h2
      obtain ⟨b3, s3, k3, z3⟩ := AM.bind_ok z2
      obtain ⟨p3, rfl⟩ := RC.hasFvarFast_pstep p2.ok (denote_ext hy (p1.ext.trans p2.ext)) k3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
      refine ⟨(p1.trans p2).trans p3, ?_⟩
      simp only [Bool.not_eq_true] at h2
      simp [h1, h2]
  · rename_i h1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    simp only [Bool.not_eq_true] at h1
    exact ⟨p1, by simp [h1]⟩

section Knot

variable {env : Env}

/-! ## The stored type -/

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:41-55 recDomsAt
con-leche: ConLeche/Verify/Cached/GenRecC.lean:736 recDomsAtS_spec — the stored
domains against the generated ones, binder by binder, both telescopes' types
scoped at their own binders. -/
theorem recDomsAt_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (rec : ConLeche.Name) (sfvs gfvs : List EIdx) (sfvsP gfvsP : List Expr)
    (hcs : ∀ (i : Nat) (x : Expr), sfvsP[i]? = some x → Expr.WScoped i x.fvarTypeD)
    (hcg : ∀ (i : Nat) (x : Expr), gfvsP[i]? = some x → Expr.WScoped i x.fvarTypeD) :
    ∀ (k j : Nat), CSpecF env fe
      (fun st => Frontend.denoteEList st sfvs = some sfvsP ∧
        Frontend.denoteEList st gfvs = some gfvsP)
      (Arena.recDomsAt .verified fe sfvs gfvs j k) (fun _ _ _ => True)
      (ConLeche.recDomsAt (fueledOpsM .verified) env rec sfvsP gfvsP j k) := by
  intro k
  induction k with
  | zero =>
    intro j s₀ s' r hok _ hrun
    simp only [Arena.recDomsAt] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨CoreStep.refl hok, (), trivial, ?_⟩
    simp only [ConLeche.recDomsAt]
    exact FOk.pure ()
  | succ k ih =>
    intro j s₀ s' r hok hpre hrun
    obtain ⟨hs, hg⟩ := hpre
    simp only [Arena.recDomsAt] at hrun
    cases h1 : sfvs[j]? with
    | none =>
      rw [h1] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
    | some sv =>
    cases h2 : gfvs[j]? with
    | none =>
      rw [h1, h2] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
    | some gv =>
    rw [h1, h2] at hrun
    dsimp only at hrun
    obtain ⟨a, ha, hda⟩ := (denoteEList_getElem? hs j).2 sv h1
    obtain ⟨b, hb, hdb⟩ := (denoteEList_getElem? hg j).2 gv h2
    obtain ⟨a', s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, ha'⟩ := fvarTypeD_run hok.state hda k1
    rw [hs1] at z1
    obtain ⟨b', s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨hs2, hb'⟩ := fvarTypeD_run hok.state hdb k2
    rw [hs2] at z2
    obtain ⟨v, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨c3, hF3⟩ := defeq_crun (hk.knot env fe henv) hok ha' hb' (hcs j a ha)
      (hcg j b hb) k3
    obtain ⟨hv, z4⟩ := AM.dunless_ok AM.Never.fail_any z3
    replace z4 := AM.pure_bind_ok z4
    obtain ⟨c4, _, -, hF4⟩ := ih (j + 1) s3 s' r c3.ok
      ⟨denoteEList_ext c3.ext _ _ hs, denoteEList_ext c3.ext _ _ hg⟩ z4
    refine ⟨c3.trans c4, (), trivial, ?_⟩
    simp only [ConLeche.recDomsAt, ha, hb]
    subst hv
    exact FOk.bind FOk.unwrapOr (FOk.bind FOk.unwrapOr (FOk.bind hF3
      (by simp only [↓reduceIte]; exact FOk.seq (FOk.pure ()) hF4)))

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:57-70 recTyOpened
con-leche: ConLeche/Verify/Cached/GenRecC.lean:754 recTyOpenedS_spec — the two
telescopes opened at their own locals: the domains, then the residues. -/
theorem recTyOpened_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (rec : ConLeche.Name) (n : Nat) (sP gP : Expr) (hws : Expr.WScoped 0 sP)
    (hwg : Expr.WScoped 0 gP) (so go : Option (List EIdx × EIdx)) :
    CSpecF env fe
      (fun st => denoteOpen st so = some (ConLeche.openPisAtFvars n sP 0) ∧
        denoteOpen st go = some (ConLeche.openPisAtFvars n gP 0))
      (Arena.recTyOpened .verified fe n so go) (fun _ _ _ => True)
      (ConLeche.recTyOpened (fueledOpsM .verified) env rec n (ConLeche.openPisAtFvars n sP 0)
        (ConLeche.openPisAtFvars n gP 0)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hso, hgo⟩ := hpre
  cases so with
  | none =>
    simp only [Arena.recTyOpened] at hrun
    exact absurd hrun (fun hc => AM.fail_ok hc)
  | some qs =>
  obtain ⟨sfvs, srest⟩ := qs
  cases go with
  | none =>
    simp only [Arena.recTyOpened] at hrun
    exact absurd hrun (fun hc => AM.fail_ok hc)
  | some qg =>
  obtain ⟨gfvs, grest⟩ := qg
  obtain ⟨sfvsP, srestP, hos, hsf, hsr⟩ := denoteOpen_some_inv hso
  obtain ⟨gfvsP, grestP, hog, hgf, hgr⟩ := denoteOpen_some_inv hgo
  have hcs : ∀ (i : Nat) (x : Expr), sfvsP[i]? = some x → Expr.WScoped i x.fvarTypeD :=
    fun i x hx => by simpa using ConLeche.Cached.openers_fvarTypeD_WScoped hos hws hx
  have hcg : ∀ (i : Nat) (x : Expr), gfvsP[i]? = some x → Expr.WScoped i x.fvarTypeD :=
    fun i x hx => by simpa using ConLeche.Cached.openers_fvarTypeD_WScoped hog hwg hx
  have hrs : Expr.WScoped n srestP := by
    simpa using (ConLeche.openPisAtFvars_WScoped n sP 0 hos hws).2
  have hrg : Expr.WScoped n grestP := by
    simpa using (ConLeche.openPisAtFvars_WScoped n gP 0 hog hwg).2
  simp only [Arena.recTyOpened] at hrun
  obtain ⟨_, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨c1, _, -, hF1⟩ := recDomsAt_spec fe hk henv rec sfvs gfvs sfvsP gfvsP hcs hcg n 0
    s₀ s1 _ hok ⟨hsf, hgf⟩ k1
  obtain ⟨v, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨c2, hF2⟩ := defeq_crun (hk.knot env fe henv) c1.ok (denote_ext hsr c1.ext)
    (denote_ext hgr c1.ext) hrs hrg k2
  obtain ⟨hv, z3⟩ := AM.dunless_ok (AM.Never.fail _) z2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
  refine ⟨c1.trans c2, (), trivial, ?_⟩
  rw [hos, hog]
  simp only [ConLeche.recTyOpened]
  subst hv
  exact FOk.bind hF1 (FOk.bind hF2 (by simp only [↓reduceIte]; exact FOk.pure ()))

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:72-86 recTyCheck
con-leche: ConLeche/Verify/Cached/GenRecC.lean:790 recTyCheckS_spec — **the stored
type's check**: closed, at the record's level parameters, resolving, inferred, a
sort, and the generated one binder by binder up to the major. -/
theorem recTyCheck_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (rec : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name) (n : Nat) (s g : EIdx)
    (sP gP : Expr) :
    CSpecF env fe
      (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st s = some sP ∧
        denoteE st g = some gP)
      (Arena.recTyCheck .verified fe lps n s g) (fun _ _ _ => True)
      (ConLeche.recTyCheck (fueledOpsM .verified) (mkFEnv env) rec lpsP n sP gP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hlps, hs, hg⟩ := hpre
  simp only [Arena.recTyCheck] at hrun
  -- closed
  obtain ⟨b1, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, rfl⟩ := streamClosed_run hok.state hs hg k1
  obtain ⟨hcl, z2⟩ := AM.dunless_ok AM.Never.fail_any z1
  replace z2 := AM.pure_bind_ok z2
  have hfs : sP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcl; exact hcl.1.2
  have hfg : gP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcl; exact hcl.2
  have hws : Expr.WScoped 0 sP := ConLeche.Expr.WScoped.of_not_hasFvar hfs
  have hwg : Expr.WScoped 0 gP := ConLeche.Expr.WScoped.of_not_hasFvar hfg
  -- the level parameters
  obtain ⟨b2, s2, k2, z3⟩ := AM.bind_ok z2
  obtain ⟨h2st, h2c, h2p, rfl⟩ := allLevelParamsDefined_run p1.ok
    (denoteNList_ext p1.ext.lss.ls.ns _ _ hlps) (denote_ext hs p1.ext) k2
  obtain ⟨hlp, z4⟩ := AM.dunless_ok AM.Never.fail_any z3
  replace z4 := AM.pure_bind_ok z4
  have p2 : PStep s1 s2 := PStep.of_caches ⟨by rw [h2st]; exact p1.ok.wf⟩
    (by rw [h2st]; exact Ext.refl _) h2c h2p
  have c2 := (p1.trans p2).toCore hok
  -- the resolution
  obtain ⟨b3, s3, k3, z5⟩ := AM.bind_ok z4
  obtain ⟨p3, rfl⟩ := constsResolveFFast_pstep c2.ok.toR (denote_ext hs c2.ext) k3
  obtain ⟨hcr, z6⟩ := AM.dunless_ok (AM.Never.bind fun _ => AM.Never.fail_any) z5
  replace z6 := AM.pure_bind_ok z6
  have c3 := c2.trans (p3.toCore c2.ok)
  -- a type
  obtain ⟨st, s4, k4, z7⟩ := AM.bind_ok z6
  obtain ⟨c4, stP, hstP, hwst, hF4⟩ := infer_crun hk henv c3.ok (denote_ext hs c3.ext) hws k4
  obtain ⟨u, s5, k5, z8⟩ := AM.bind_ok z7
  obtain ⟨c5, uP, -, hF5⟩ := ensureSort_crun hk henv c4.ok hstP hwst k5
  have c15 := (c3.trans c4).trans c5
  -- the two openings
  obtain ⟨so, s6, k6, z9⟩ := AM.bind_ok z8
  obtain ⟨p6, hso⟩ := openPisAtFvars_run n c5.ok.state (denote_ext hs c15.ext) k6
  obtain ⟨go, s7, k7, z10⟩ := AM.bind_ok z9
  obtain ⟨p7, hgo⟩ := openPisAtFvars_run n p6.ok (denote_ext hg (c15.ext.trans p6.ext)) k7
  have c7 := (p6.trans p7).toCore c5.ok
  obtain ⟨c8, _, -, hF8⟩ := recTyOpened_spec fe hk henv rec n sP gP hws hwg so go s7 s' r c7.ok
    ⟨denoteOpen_ext p7.ext _ _ hso, hgo⟩ z10
  refine ⟨(c15.trans c7).trans c8, (), trivial, ?_⟩
  simp only [ConLeche.recTyCheck, hcl, hlp, constsResolveF_eq, hcr,
    mkFEnv_env, ↓reduceIte]
  exact FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ())
    (FOk.bind hF4 (FOk.bind hF5 hF8))))

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:88-109 ruleAgree
con-leche: ConLeche/Verify/Cached/GenRecC.lean:802 ruleAgreeS_spec — **one stored
rule's check**. -/
theorem ruleAgree_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (rec ctor : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name) (s g : EIdx)
    (sP gP : Expr) :
    CSpecF env fe
      (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st s = some sP ∧
        denoteE st g = some gP)
      (Arena.ruleAgree .verified fe lps s g) (fun _ _ _ => True)
      (ConLeche.ruleAgree (fueledOpsM .verified) (mkFEnv env) rec ctor lpsP sP gP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hlps, hs, hg⟩ := hpre
  simp only [Arena.ruleAgree] at hrun
  obtain ⟨b1, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, rfl⟩ := streamClosed_run hok.state hs hg k1
  obtain ⟨hcl, z2⟩ := AM.dunless_ok AM.Never.fail_any z1
  replace z2 := AM.pure_bind_ok z2
  have hfs : sP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcl; exact hcl.1.2
  have hfg : gP.hasFvar = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcl; exact hcl.2
  have hws : Expr.WScoped 0 sP := ConLeche.Expr.WScoped.of_not_hasFvar hfs
  have hwg : Expr.WScoped 0 gP := ConLeche.Expr.WScoped.of_not_hasFvar hfg
  obtain ⟨b2, s2, k2, z3⟩ := AM.bind_ok z2
  obtain ⟨h2st, h2c, h2p, rfl⟩ := allLevelParamsDefined_run p1.ok
    (denoteNList_ext p1.ext.lss.ls.ns _ _ hlps) (denote_ext hs p1.ext) k2
  obtain ⟨hlp, z4⟩ := AM.dunless_ok AM.Never.fail_any z3
  replace z4 := AM.pure_bind_ok z4
  have p2 : PStep s1 s2 := PStep.of_caches ⟨by rw [h2st]; exact p1.ok.wf⟩
    (by rw [h2st]; exact Ext.refl _) h2c h2p
  have c2 := (p1.trans p2).toCore hok
  obtain ⟨b3, s3, k3, z5⟩ := AM.bind_ok z4
  obtain ⟨p3, rfl⟩ := constsResolveFFast_pstep c2.ok.toR (denote_ext hs c2.ext) k3
  obtain ⟨hcr, z6⟩ := AM.dunless_ok (AM.Never.bind fun _ => AM.Never.fail_any) z5
  replace z6 := AM.pure_bind_ok z6
  have c3 := c2.trans (p3.toCore c2.ok)
  obtain ⟨ts, s4, k4, z7⟩ := AM.bind_ok z6
  obtain ⟨c4, tsP, htsP, hwts, hF4⟩ := infer_crun hk henv c3.ok (denote_ext hs c3.ext) hws k4
  have c14 := c3.trans c4
  obtain ⟨tg, s5, k5, z8⟩ := AM.bind_ok z7
  obtain ⟨c5, tgP, htgP, hwtg, hF5⟩ := infer_crun hk henv c4.ok (denote_ext hg c14.ext) hwg k5
  have c15 := c14.trans c5
  obtain ⟨v1, s6, k6, z9⟩ := AM.bind_ok z8
  obtain ⟨c6, hF6⟩ := defeq_crun (hk.knot env fe henv) c5.ok (denote_ext htsP c5.ext) htgP
    hwts hwtg k6
  obtain ⟨hv1, z10⟩ := AM.dunless_ok AM.Never.fail_any z9
  replace z10 := AM.pure_bind_ok z10
  have c16 := c15.trans c6
  obtain ⟨v2, s7, k7, z11⟩ := AM.bind_ok z10
  obtain ⟨c7, hF7⟩ := defeq_crun (hk.knot env fe henv) c6.ok (denote_ext hs c16.ext)
    (denote_ext hg c16.ext) hws hwg k7
  obtain ⟨hv2, z12⟩ := AM.dunless_ok (AM.Never.fail _) z11
  obtain ⟨rfl, rfl⟩ := AM.pure_ok z12
  refine ⟨c16.trans c7, (), trivial, ?_⟩
  simp only [ConLeche.ruleAgree, hcl, hlp, constsResolveF_eq, hcr,
    mkFEnv_env, ↓reduceIte]
  subst hv1 hv2
  exact FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ())
    (FOk.bind hF4 (FOk.bind hF5 (FOk.bind hF6 (by
      simp only [↓reduceIte]
      exact FOk.seq (FOk.pure ()) (FOk.bind hF7 (by
        simp only [↓reduceIte]; exact FOk.pure ()))))))))

end Knot

/-! ## The stored major's container -/

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:111-128 streamNestedOk —
the major's domain against the firing data. -/
theorem streamNestedDom_run {s₀ s' : AState} {dom : EIdx} {domP : Expr} {n : Nat}
    {lvls : List LIdx} {lvlsP : List Level} {pins : List EIdx} {pinsP : List Expr} {r : Bool}
    (hok : StateOK s₀) (hd : denoteE s₀.store dom = some domP)
    (hl : denoteLList s₀.store.ls lvls = some lvlsP)
    (hp : Frontend.denoteEList s₀.store pins = some pinsP)
    (hrun : Arena.streamNestedDom dom n lvls pins s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r = ((match domP.getAppFn with
        | .const _ us => us == lvlsP
        | _ => false) &&
      domP.getAppArgs == pinsP.map (Expr.liftLooseBVars n 0) ++
        (List.range n).map (fun i => Expr.bvar (n - 1 - i))) := by
  simp only [Arena.streamNestedDom] at hrun
  obtain ⟨hh, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hhd⟩ := getAppFn_run hok hd k1
  by_cases htc : (hh.tag == ETag.const) = true
  · rw [ite_eq_left htc] at z1
    obtain ⟨o, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨rfl, ho⟩ := viewConst_run k2
    cases o with
    | none => exact absurd z2 (fun hc => failDanglingE_ok hc)
    | some q =>
    obtain ⟨cn, us⟩ := q
    obtain ⟨nm, ls, hgl, -, hls⟩ := denote_const_inv hok.wf (view_of_viewConst_tag htc ho.symm) hhd
    dsimp only at z2
    obtain ⟨usv, s3, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨rfl, hv⟩ := viewLs_run k3
    have hll := denoteLs_of_view hv hls
    rw [hgl]
    dsimp only
    rw [beq_of_denoteLList hok.wf hll hl] at z3
    by_cases hq : (ls == lvlsP) = true
    · rw [ite_eq_left hq] at z3
      obtain ⟨args, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨rfl, hargs⟩ := getAppArgs_run hok hd k4
      obtain ⟨ps, s5, k5, z5⟩ := AM.bind_ok z4
      obtain ⟨p5, hps⟩ := liftList_run n pins pinsP _ s5 ps hok hp k5
      obtain ⟨bs, s6, k6, z6⟩ := AM.bind_ok z5
      obtain ⟨p6, hbs⟩ := bvarList_run n (List.range n) s5 s6 bs p5.ok k6
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z6
      refine ⟨p5.trans p6, ?_⟩
      have happ := denoteEList_append (denoteEList_ext p6.ext _ _ hps) hbs
      rw [beq_of_denoteEList p6.ok.wf (denoteEList_ext (p5.ext.trans p6.ext) _ _ hargs) happ, hq,
        Bool.true_and]
    · rw [ite_eq_right hq] at z3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
      simp only [Bool.not_eq_true] at hq
      exact ⟨PStep.refl hok, by rw [hq, Bool.false_and]⟩
  · rw [ite_eq_right htc] at z1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨PStep.refl hok, ?_⟩
    cases hgl : domP.getAppFn with
    | const n us =>
      rw [hgl] at hhd
      exact absurd (by simpa using tag_const_of_denote hok.wf hhd) htc
    | _ => rfl

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:111-128 streamNestedOk —
**an auxiliary recursor's stored type fires where the generated one does**. -/
theorem streamNestedOk_run {s₀ s' : AState} {ty : EIdx} {tyP : Expr} {mI rP : Nat}
    {fire : IRecRuleFire} {fireP : RecRuleFire} {r : Bool} (hok : StateOK s₀)
    (hty : denoteE s₀.store ty = some tyP) (hf : Frontend.denoteFire s₀.store fire = some fireP)
    (hrun : Arena.streamNestedOk ty mI rP fire s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ r = ConLeche.streamNestedOk tyP mI rP fireP := by
  cases fire with
  | plain =>
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    subst hf
    simp only [Arena.streamNestedOk] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | levels lvls =>
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨ls, -, rfl⟩ := hf
    simp only [Arena.streamNestedOk] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | nested lvls pins =>
    simp only [Frontend.denoteFire] at hf
    cases hls : denoteLList s₀.store.ls lvls with
    | none => rw [hls] at hf; exact nomatch hf
    | some ls =>
    cases hps : Frontend.denoteEList s₀.store pins with
    | none => rw [hls, hps] at hf; exact nomatch hf
    | some ps =>
    rw [hls, hps] at hf
    obtain rfl := (Option.some.inj hf).symm
    simp only [Arena.streamNestedOk] at hrun
    obtain ⟨o, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, ho⟩ := stripPis_pstep hok hty k1
    rw [hs1] at z1
    simp only [ConLeche.streamNestedOk]
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [stripPis_none ho]
    | some q =>
      obtain ⟨pre, rest⟩ := q
      obtain ⟨preP, restP, hsl, -, hrest⟩ := denoteBP_some ho
      rw [hsl]
      dsimp only at z1 ⊢
      by_cases htg : (rest.tag == ETag.forallE) = true
      · rw [ite_eq_left htg] at z1
        obtain ⟨o2, s2, k2, z2⟩ := AM.bind_ok z1
        obtain ⟨hs2, ho2⟩ := viewBind_run k2
        rw [hs2] at z2
        cases o2 with
        | none => exact absurd z2 (fun hc => failDanglingE_ok hc)
        | some q2 =>
        obtain ⟨dom, body⟩ := q2
        obtain ⟨domP, bodyP, rfl, hdd, -⟩ := denote_forallE_inv hok.wf
          (view_forallE_of_viewBind htg ho2.symm) hrest
        dsimp only at z2 ⊢
        exact streamNestedDom_run hok hdd hls hps z2
      · rw [ite_eq_right htg] at z1
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
        refine ⟨PStep.refl hok, ?_⟩
        cases restP with
        | forallE d b => exact absurd (by simpa using tag_forallE_of_denote hok.wf hrest) htg
        | _ => rfl

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:130-135 generatedFire —
the firing mode the generated recursor's rules carry at its major. -/
theorem generatedFire_run {s₀ s' : AState} {M : Arena.TargetMajor} {MP : ConLeche.TargetMajor}
    {rP : Nat} {r : IRecRuleFire} (hok : StateOK s₀) (hM : dMajor s₀.store M = some MP)
    (hrun : Arena.generatedFire M rP s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ Frontend.denoteFire s'.store r = some (ConLeche.generatedFire MP rP) := by
  obtain ⟨-, -, -, -, -, -, hmem, -, -⟩ := dMajor_inv hM
  simp only [Arena.generatedFire] at hrun
  simp only [ConLeche.generatedFire, ← hmem]
  cases hm : M.member with
  | none =>
    rw [hm] at hrun
    exact auxRuleFire_run M MP rP s₀ s' r hok hM hrun
  | some k =>
    rw [hm] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩

/-! ## The stored rules -/

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:137-149 streamRulesShape —
one rule per constructor of the class, in order, each with its field count.
Reads nothing but the store's name table. -/
theorem streamRulesShape_run (rec : ConLeche.Name) :
    ∀ (rs : List IRecRule) (rsP : List RecRule) (cs : List (IConstantVal × Nat))
      (csP : List (ConstantVal × Nat)) (s₀ s' : AState) (r : Unit), StateOK s₀ →
      Frontend.denoteRules s₀.store rs = some rsP → dCtors s₀.store cs = some csP →
      Arena.streamRulesShape rs cs s₀ = .ok (r, s') →
      s' = s₀ ∧ FOk (ConLeche.streamRulesShape (m := FueledM) rec rsP csP) () := by
  intro rs
  induction rs with
  | nil =>
    intro rsP cs csP s₀ s' r hok hr hc hrun
    obtain rfl := denoteRules_nil_inv hr
    cases cs with
    | nil =>
      obtain rfl := mapM_option_nil_inv hc
      simp only [Arena.streamRulesShape] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.streamRulesShape]
      exact FOk.pure ()
    | cons _ _ =>
      simp only [Arena.streamRulesShape] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
  | cons x rs ih =>
    intro rsP cs csP s₀ s' r hok hr hc hrun
    cases cs with
    | nil =>
      simp only [Arena.streamRulesShape] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
    | cons c cs =>
      obtain ⟨y, ys, rfl, hy, hys⟩ := denoteRules_cons_inv hr
      obtain ⟨cP, csP', rfl, hcP, hcs⟩ := mapM_option_cons_inv hc
      simp only [Arena.streamRulesShape] at hrun
      obtain ⟨hyc, -, -, hnf⟩ := denoteRule_inv hy
      simp only [dCtor, Option.map_eq_some_iff] at hcP
      obtain ⟨cvP, hcv, rfl⟩ := hcP
      have hn := beq_handle_eq hok.wf hyc (denoteCV_name hcv)
      obtain ⟨hg, z1⟩ := AM.dunless_ok AM.Never.fail_any hrun
      replace z1 := AM.pure_bind_ok z1
      obtain ⟨rfl, hF⟩ := ih ys cs csP' s₀ s' r hok hys hcs z1
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.streamRulesShape]
      rw [hn, hnf] at hg
      rw [ite_eq_left hg]
      exact FOk.seq (FOk.pure ()) hF

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:499-508 ruleBinds —
**a rule binds its arguments**: the twin's `stripLams` count is con-leche's,
read-only. -/
theorem ruleBinds_run {rec : ConLeche.Name} {rP : Nat} {r : IRecRule} {rl : RecRule}
    {s₀ s' : AState} {u : Unit} (hok : StateOK s₀)
    (hr : Frontend.denoteRule s₀.store r = some rl)
    (hrun : Arena.ruleBinds rP r s₀ = .ok (u, s')) :
    s' = s₀ ∧ FOk (ConLeche.ruleBinds (m := FueledM) rec rP rl) () := by
  obtain ⟨-, -, hrhs, hnf⟩ := denoteRule_inv hr
  simp only [Arena.ruleBinds] at hrun
  obtain ⟨o, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hbp⟩ := stripLams_pstep hok hrhs k1
  cases o with
  | none => exact absurd z1 (fun hc => AM.fail_ok hc)
  | some p =>
    obtain ⟨-, rfl⟩ := AM.pure_ok z1
    have hsome : (rl.rhs.stripLams (rP + rl.nfields)).isSome = true := by
      rw [← hnf]
      obtain ⟨bs, e⟩ := p
      simp only [ExprOps.denoteBP] at hbp
      split at hbp
      · rw [← Option.some.inj hbp]; rfl
      · simp at hbp
    refine ⟨rfl, ?_⟩
    simp only [ConLeche.ruleBinds, hsome]
    exact FOk.pure ()


section Knot

variable {env : Env}

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:154-165 streamRulesCheck
con-leche: ConLeche/Verify/Cached/GenRecC.lean:814 streamRulesCheckS_spec — each
stored rule binds its arguments and agrees with the generated right-hand side at
its position. -/
theorem streamRulesCheck_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (rec : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name) (rP : Nat) :
    ∀ (rs : List IRecRule) (rsP : List RecRule) (gs : List EIdx) (gsP : List Expr),
      CSpecF env fe
        (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
          Frontend.denoteRules st rs = some rsP ∧ Frontend.denoteEList st gs = some gsP)
        (Arena.streamRulesCheck .verified fe lps rP rs gs) (fun _ _ _ => True)
        (ConLeche.streamRulesCheck (fueledOpsM .verified) (mkFEnv env) rec lpsP rP rsP gsP) := by
  intro rs
  induction rs with
  | nil =>
    intro rsP gs gsP s₀ s' r hok hpre hrun
    obtain ⟨-, hr, hg⟩ := hpre
    obtain rfl := denoteRules_nil_inv hr
    cases gs with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at hg
      subst hg
      simp only [Arena.streamRulesCheck] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨CoreStep.refl hok, (), trivial, ?_⟩
      simp only [ConLeche.streamRulesCheck]
      exact FOk.pure ()
    | cons _ _ =>
      simp only [Arena.streamRulesCheck] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
  | cons x rs ih =>
    intro rsP gs gsP s₀ s' r hok hpre hrun
    obtain ⟨hlps, hr, hg⟩ := hpre
    cases gs with
    | nil =>
      simp only [Arena.streamRulesCheck] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
    | cons g gs =>
      obtain ⟨y, ys, rfl, hy, hys⟩ := denoteRules_cons_inv hr
      simp only [Frontend.denoteEList] at hg
      cases h1 : denoteE s₀.store g with
      | none => rw [h1] at hg; simp at hg
      | some gP =>
      cases h2 : Frontend.denoteEList s₀.store gs with
      | none => rw [h1, h2] at hg; simp at hg
      | some gsP' =>
      rw [h1, h2] at hg
      obtain rfl := (Option.some.inj hg).symm
      obtain ⟨hyc, -, hyr, -⟩ := denoteRule_inv hy
      simp only [Arena.streamRulesCheck] at hrun
      simp only [ConLeche.streamRulesCheck]
      obtain ⟨_, s0, k0, z0⟩ := AM.bind_ok hrun
      obtain ⟨hs0, hF0⟩ := ruleBinds_run (rec := rec) hok.state hy k0
      rw [hs0] at z0
      clear hrun
      have hrun := z0
      rw [beq_of_denoteE hok.state.wf hyr h1] at hrun
      by_cases hq : (y.rhs == gP) = true
      · rw [ite_eq_left hq] at hrun
        replace hrun := AM.pure_bind_ok hrun
        obtain ⟨c1, _, -, hF⟩ := ih ys gs gsP' s₀ s' r hok ⟨hlps, hys, h2⟩ hrun
        refine ⟨c1, (), trivial, ?_⟩
        rw [ite_eq_left hq]
        exact FOk.seq hF0 (FOk.seq (FOk.pure ()) hF)
      · rw [ite_eq_right hq] at hrun
        obtain ⟨_, s1, k1, z1⟩ := AM.bind_ok hrun
        obtain ⟨c1, _, -, hF1⟩ := ruleAgree_spec fe hk henv rec y.ctor lps lpsP _ _ _ _ s₀ s1 _
          hok ⟨hlps, hyr, h1⟩ k1
        obtain ⟨c2, _, -, hF2⟩ := ih ys gs gsP' s1 s' r c1.ok
          ⟨denoteNList_ext c1.ext.lss.ls.ns _ _ hlps, denoteRules_ext c1.ext _ _ hys,
            denoteEList_ext c1.ext _ _ h2⟩ z1
        refine ⟨c1.trans c2, (), trivial, ?_⟩
        rw [ite_eq_right hq]
        exact FOk.seq hF0 (FOk.seq hF1 hF2)

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:162-167 streamRecCompare
con-leche: ConLeche/Verify/Cached/GenRecC.lean:843 streamRecCompareS_spec — one
recursor's comparison: its stored type unless it is the generated one, and its
stored rules. -/
theorem streamRecCompare_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (rc : Arena.RecShape) (rcP : ConLeche.RecShape)
    (g : IConstantVal × Arena.TargetMajor × List EIdx)
    (gP : ConstantVal × ConLeche.TargetMajor × List Expr) :
    CSpecF env fe (fun st => dRec st rc = some rcP ∧ dRecOut st g = some gP)
      (Arena.streamRecCompare .verified fe rc g) (fun _ _ _ => True)
      (ConLeche.streamRecCompare (fueledOpsM .verified) (mkFEnv env) rcP gP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrc, hg⟩ := hpre
  obtain ⟨hcv, hrP, hmI, -, hrules, -⟩ := dRec_inv hrc
  obtain ⟨hcvG, hM, hrh⟩ := RC.dRecOut_inv hg
  simp only [Arena.streamRecCompare] at hrun
  simp only [ConLeche.streamRecCompare, ← hrP]
  obtain ⟨hnmG, hlpsG, htyG⟩ := Core.denoteCV_inv hcvG
  have hty := denoteCV_type hcv
  rw [beq_of_denoteE hok.state.wf hty htyG] at hrun
  by_cases hq : (rcP.cvR.type == gP.1.type) = true
  · rw [ite_eq_left hq] at hrun
    replace hrun := AM.pure_bind_ok hrun
    obtain ⟨c1, _, -, hF⟩ := streamRulesCheck_spec fe hk henv gP.1.name _ _ rc.rP _ _ _ _ s₀ s' r hok
      ⟨hlpsG, hrules, hrh⟩ hrun
    refine ⟨c1, (), trivial, ?_⟩
    rw [ite_eq_left hq]
    exact FOk.seq (FOk.pure ()) hF
  · rw [ite_eq_right hq] at hrun
    obtain ⟨_, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨c1, _, -, hF1⟩ := recTyCheck_spec fe hk henv gP.1.name _ _ (rc.mI + 1) _ _ _ _ s₀ s1 _
      hok ⟨hlpsG, hty, htyG⟩ k1
    obtain ⟨c2, _, -, hF2⟩ := streamRulesCheck_spec fe hk henv gP.1.name _ _ rc.rP _ _ _ _ s1 s' r c1.ok
      ⟨denoteNList_ext c1.ext.lss.ls.ns _ _ hlpsG, denoteRules_ext c1.ext _ _ hrules,
        denoteEList_ext c1.ext _ _ hrh⟩ z1
    refine ⟨c1.trans c2, (), trivial, ?_⟩
    rw [ite_eq_right hq, ← hmI]
    exact FOk.seq hF1 hF2

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:169-178 streamRecCheck
con-leche: ConLeche/Verify/Cached/GenRecC.lean:875 streamRecCheckS_spec — **one
recursor, stored against generated**. -/
theorem streamRecCheck_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env)
    (rc : Arena.RecShape) (rcP : ConLeche.RecShape)
    (g : IConstantVal × Arena.TargetMajor × List EIdx)
    (gP : ConstantVal × ConLeche.TargetMajor × List Expr) :
    CSpecF env fe (fun st => dRec st rc = some rcP ∧ dRecOut st g = some gP)
      (Arena.streamRecCheck .verified fe rc g) (fun _ _ _ => True)
      (ConLeche.streamRecCheck (fueledOpsM .verified) (mkFEnv env) rcP gP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrc, hg⟩ := hpre
  obtain ⟨hcv, hrP, hmI, -, hrules, -⟩ := dRec_inv hrc
  obtain ⟨hcvG, hM, hrh⟩ := RC.dRecOut_inv hg
  obtain ⟨-, -, -, -, -, hcs, -⟩ := dMajor_inv hM
  simp only [Arena.streamRecCheck] at hrun
  obtain ⟨_, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hF1⟩ := streamRulesShape_run rcP.cvR.name rc.rules rcP.rules g.2.1.ctors
    gP.2.1.ctors s₀ s1 _ hok.state hrules hcs k1
  rw [hs1] at z1
  obtain ⟨fire, s2, k2, z2⟩ := AM.bind_ok z1
  obtain ⟨p2, hfire⟩ := generatedFire_run hok.state hM k2
  obtain ⟨b3, s3, k3, z3⟩ := AM.bind_ok z2
  obtain ⟨p3, rfl⟩ := streamNestedOk_run p2.ok (denote_ext (denoteCV_type hcv) p2.ext) hfire k3
  obtain ⟨hn, z4⟩ := AM.dunless_ok AM.Never.fail_any z3
  replace z4 := AM.pure_bind_ok z4
  have c3 := (p2.trans p3).toCore hok
  obtain ⟨c4, _, -, hF4⟩ := streamRecCompare_spec fe hk henv rc rcP g gP s3 s' r c3.ok
    ⟨dRec_ext c3.ext _ _ hrc, dRecOut_ext c3.ext _ _ hg⟩ z4
  refine ⟨c3.trans c4, (), trivial, ?_⟩
  simp only [ConLeche.streamRecCheck]
  rw [← hmI, ← hrP]
  rw [ite_eq_left hn]
  exact FOk.seq hF1 (FOk.seq (FOk.pure ()) hF4)

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:180-188 streamRecsCheck
con-leche: ConLeche/Verify/Cached/GenRecC.lean:882 streamRecsCheckS_spec — **THEOREM 1
for the block's stored recursors against the generated ones**, record by record. -/
theorem streamRecsCheck_spec (fe : IFEnv) (hk : CoreSpec Arena.checkFuel) (henv : EnvWF env) :
    ∀ (recs : List Arena.RecShape) (recsP : List ConLeche.RecShape)
      (out : List (IConstantVal × Arena.TargetMajor × List EIdx))
      (outP : List (ConstantVal × ConLeche.TargetMajor × List Expr)),
      CSpecF env fe
        (fun st => recs.mapM (dRec st) = some recsP ∧ out.mapM (dRecOut st) = some outP)
        (Arena.streamRecsCheck .verified fe recs out) (fun _ _ _ => True)
        (ConLeche.streamRecsCheck (fueledOpsM .verified) (mkFEnv env) recsP outP) := by
  intro recs
  induction recs with
  | nil =>
    intro recsP out outP s₀ s' r hok hpre hrun
    obtain ⟨hr, ho⟩ := hpre
    obtain rfl := mapM_option_nil_inv hr
    cases out with
    | nil =>
      obtain rfl := mapM_option_nil_inv ho
      simp only [Arena.streamRecsCheck] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨CoreStep.refl hok, (), trivial, ?_⟩
      simp only [ConLeche.streamRecsCheck]
      exact FOk.pure ()
    | cons _ _ =>
      simp only [Arena.streamRecsCheck] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
  | cons rc rcs ih =>
    intro recsP out outP s₀ s' r hok hpre hrun
    obtain ⟨hr, ho⟩ := hpre
    cases out with
    | nil =>
      simp only [Arena.streamRecsCheck] at hrun
      exact absurd hrun (fun hc => AM.fail_ok hc)
    | cons g gs =>
      obtain ⟨rcP, rcsP, rfl, hrc, hrcs⟩ := mapM_option_cons_inv hr
      obtain ⟨gP, gsP, rfl, hgP, hgs⟩ := mapM_option_cons_inv ho
      simp only [Arena.streamRecsCheck] at hrun
      obtain ⟨_, s1, k1, z1⟩ := AM.bind_ok hrun
      obtain ⟨c1, _, -, hF1⟩ := streamRecCheck_spec fe hk henv rc rcP g gP s₀ s1 _ hok ⟨hrc, hgP⟩ k1
      obtain ⟨c2, _, -, hF2⟩ := ih rcsP gs gsP s1 s' r c1.ok
        ⟨dRec_ext.list c1.ext _ _ hrcs, dRecOut_ext.list c1.ext _ _ hgs⟩ z1
      refine ⟨c1.trans c2, (), trivial, ?_⟩
      simp only [ConLeche.streamRecsCheck]
      exact FOk.seq hF1 hF2

end Knot

/-! ## The K flags -/

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:190-201 streamKCheck —
**the records' K flags against the block**: each record's flag is the one the
generated recursor has (`recKExpected_eq`).  Reads nothing of the state. -/
theorem streamKCheck_run {p : Arena.BlockShape} {pP : ConLeche.BlockShape} :
    ∀ (recs : List Arena.RecShape) (recsP : List ConLeche.RecShape)
      (out : List (IConstantVal × Arena.TargetMajor × List EIdx))
      (outP : List (ConstantVal × ConLeche.TargetMajor × List Expr)) (s₀ s' : AState) (r : Unit),
      dShape s₀.store p = some pP → recs.mapM (dRec s₀.store) = some recsP →
      out.mapM (dRecOut s₀.store) = some outP →
      Arena.streamKCheck p recs out s₀ = .ok (r, s') →
      s' = s₀ ∧ FOk (ConLeche.streamKCheck (m := FueledM) pP recsP outP) () := by
  intro recs
  induction recs with
  | nil =>
    intro recsP out outP s₀ s' r _ hr _ hrun
    obtain rfl := mapM_option_nil_inv hr
    simp only [Arena.streamKCheck] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, by simp only [ConLeche.streamKCheck]; exact FOk.pure ()⟩
  | cons rc rcs ih =>
    intro recsP out outP s₀ s' r hp hr ho hrun
    obtain ⟨rcP, rcsP, rfl, hrc, hrcs⟩ := mapM_option_cons_inv hr
    cases out with
    | nil =>
      obtain rfl := mapM_option_nil_inv ho
      simp only [Arena.streamKCheck] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, by simp only [ConLeche.streamKCheck]; exact FOk.pure ()⟩
    | cons g gs =>
      obtain ⟨gP, gsP, rfl, hg, hgs⟩ := mapM_option_cons_inv ho
      have hK := (dRec_inv hrc).2.2.2.2.2
      have hE := recKExpected_eq hp (RC.dRecOut_inv hg).2.1
      have hR := (dRec_inv hrc).2.2.2.2.1
      have hrE : rc.rules.isEmpty = rcP.rules.isEmpty := by
        cases h1 : rc.rules with
        | nil =>
          rw [h1] at hR
          simp only [Frontend.denoteRules, Option.some.injEq] at hR
          rw [← hR]; rfl
        | cons x xs =>
          rw [h1] at hR
          simp only [Frontend.denoteRules] at hR
          split at hR
          · rw [← Option.some.inj hR]; rfl
          · exact nomatch hR
      simp only [Arena.streamKCheck] at hrun
      split at hrun
      · exact absurd hrun (fun h => AM.fail_ok h)
      rename_i hnr
      obtain ⟨hc, z1⟩ := AM.dunless_ok AM.Never.fail_any hrun
      replace z1 := AM.pure_bind_ok z1
      obtain ⟨rfl, hF⟩ := ih rcsP gs gsP s₀ s' r hp hrcs hgs z1
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.streamKCheck]
      rw [BlockShape.noRules_spec hp, hrE] at hnr
      rw [if_neg hnr]
      rw [hK, hE] at hc
      rw [ite_eq_left hc]
      exact FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ()) hF)

/-! ## The declared feature flags -/

/-- con-leche: none — a member's constructors, denoted, keep their shape:
empty, one (with its field count), or more. -/
theorem dCtors_shape {st : EStore} {cs : List (IConstantVal × Nat)}
    {csP : List (ConstantVal × Nat)} (h : dCtors st cs = some csP) :
    (cs = [] ∧ csP = []) ∨ (∃ c cP, cs = [c] ∧ csP = [cP] ∧ cP.2 = c.2) ∨
      (∃ c d r cP dP rP, cs = c :: d :: r ∧ csP = cP :: dP :: rP) := by
  cases cs with
  | nil =>
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    exact Or.inl ⟨rfl, h.symm⟩
  | cons c rest =>
    obtain ⟨cP, restP, rfl, hcP, hrestP⟩ := mapM_option_cons_inv h
    have hc2 : cP.2 = c.2 := by
      simp only [dCtor, Option.map_eq_some_iff] at hcP
      obtain ⟨_, -, rfl⟩ := hcP; rfl
    cases rest with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrestP
      subst hrestP
      exact Or.inr (Or.inl ⟨c, cP, rfl, rfl, hc2⟩)
    | cons d r =>
      obtain ⟨dP, rP, rfl, -, -⟩ := mapM_option_cons_inv hrestP
      exact Or.inr (Or.inr ⟨c, d, r, cP, dP, rP, rfl, rfl⟩)

/-- con-leche: none — a guard that fails, passed: its condition is off. -/
theorem AM.ite_fail_ok {α : Type} {c : Bool} {e : Arena.CheckError} {k : AM α} {s s' : AState}
    {a : α} (h : (if c = true then fail e else k) s = .ok (a, s')) :
    c = false ∧ k s = .ok (a, s') := by
  cases c
  · exact ⟨rfl, by simpa using h⟩
  · exact absurd (by simpa using h) (fun h' => AM.fail_ok (α := α) h')

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:208-227 memberFlagsCheck —
**one member's flags**: the twin's three named conditions are con-leche's; the
twin reads nothing of the state. -/
theorem memberFlagsCheck_run {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    {m : Arena.MemberShape} {mP : ConLeche.MemberShape} {isRec : Bool} {i : Nat}
    {f : IndFlags} {s s' : AState} {r : Unit}
    (hp : dShape st p = some pP) (hm : dMember st m = some mP)
    (hrun : Arena.memberFlagsCheck p isRec i m f s = .ok (r, s')) :
    s' = s ∧ ConLeche.memberFlagsCheck pP isRec i mP f = .ok () := by
  have hk := BlockShape.k_spec hp
  have hip := (dShape_inv hp).2.2.2.2.2.2
  obtain ⟨-, hnI, hcs, -⟩ := dMember_inv hm
  unfold Arena.memberFlagsCheck at hrun
  obtain ⟨h1, hrun⟩ := AM.ite_fail_ok hrun
  obtain ⟨h2, hrun⟩ := AM.ite_fail_ok hrun
  obtain ⟨h3, hrun⟩ := AM.ite_fail_ok hrun
  obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
  refine ⟨rfl, ?_⟩
  unfold ConLeche.memberFlagsCheck
  rw [← hk, ← hip, ← hnI]
  rcases dCtors_shape hcs with ⟨hc, hcP⟩ | ⟨c, cP, hc, hcP, hc2⟩ | ⟨c, d, r, cP, dP, rP, hc, hcP⟩
  all_goals
    (rw [hc] at h1 h2; rw [hcP]
     clear hrun hcs hm hp
     revert h1 h2 h3
     cases f with
     | mk a b c d e =>
       cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases isRec <;>
         simp (config := { contextual := true }) [pure, Except.pure, bind, Except.bind, *])

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:229-235 membersFlagsCheck -/
theorem membersFlagsCheck_run {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    {isRec : Bool} (hp : dShape st p = some pP) :
    ∀ (i : Nat) (ms : List Arena.MemberShape) (msP : List ConLeche.MemberShape)
      (fl : List IndFlags) (s s' : AState) (r : Unit), ms.mapM (dMember st) = some msP →
      Arena.membersFlagsCheck p isRec i ms fl s = .ok (r, s') →
      s' = s ∧ ConLeche.membersFlagsCheck pP isRec i msP fl = .ok ()
  | i, [], msP, fl, s, s', r, hms, hrun => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.membersFlagsCheck] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, by simp only [ConLeche.membersFlagsCheck]; rfl⟩
  | i, m :: ms, msP, [], s, s', r, hms, hrun => by
    obtain ⟨mP, msP', rfl, -, -⟩ := mapM_option_cons_inv hms
    simp only [Arena.membersFlagsCheck] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, by simp only [ConLeche.membersFlagsCheck]; rfl⟩
  | i, m :: ms, msP, f :: fs, s, s', r, hms, hrun => by
    obtain ⟨mP, msP', rfl, hm, hms'⟩ := mapM_option_cons_inv hms
    simp only [Arena.membersFlagsCheck] at hrun
    obtain ⟨u, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨e1, h1⟩ := memberFlagsCheck_run hp hm k1
    rw [e1] at z1
    obtain ⟨rfl, h2⟩ := membersFlagsCheck_run hp (i + 1) ms msP' fs s s' r hms' z1
    refine ⟨rfl, ?_⟩
    simp only [ConLeche.membersFlagsCheck, h1, h2, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:237-288 blockFlagsCheck
(the large-eliminator clause) — the twin's verdict is con-leche's condition; a
pure step (the sort's read goes through the readback memo). -/
theorem largeElimFlagOk_run {s s' : AState} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    {f0 : IndFlags} {b : Bool} (hok : StateOK s) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hp : dShape s.store p = some pP) (hrun : Arena.largeElimFlagOk p f0 s = .ok (b, s')) :
    PStep s s' ∧
      b = (!f0.hasLargeElim || (!f0.isImpredicative && (pP.resSort.isNeverZero ||
        (pP.k == 1 && (pP.numCtors == 0 || (pP.numCtors == 1 && (f0.hasEta || f0.isK))))))) := by
  have hk := BlockShape.k_spec hp
  have hn := BlockShape.numCtors_spec hp
  unfold Arena.largeElimFlagOk at hrun
  cases hl : f0.hasLargeElim with
  | false =>
    rw [hl] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | true =>
    rw [hl] at hrun
    cases hi : f0.isImpredicative with
    | true =>
      rw [hi] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨PStep.refl hok, rfl⟩
    | false =>
      rw [hi] at hrun
      simp only [Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨l, s₁, h1, h2⟩ := AM.bind_ok hrun
      have p1 := readLevelM_pstep hok h1
      have hlv := readLevelM_denote_L hrl (PStep.refl hok) h1
      obtain ⟨-, -, -, -, hs, -, -⟩ := dShape_inv hp
      have hres : pP.resSort = l := by
        rw [hlv] at hs; exact (Option.some.inj hs).symm
      rw [hres, ← hk, ← hn]
      by_cases hz : Level.isNeverZero l = true
      · rw [ite_eq_left hz] at h2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
        exact ⟨p1, by simp [hz]⟩
      · rw [ite_eq_right hz] at h2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
        simp only [Bool.not_eq_true] at hz
        exact ⟨p1, by simp [hz]⟩

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:237-288 blockFlagsCheck
(the `for` over the classes) — the twin's `majorsFlagsCheck` reads nothing of
the state; each outside class passes both of con-leche's guards, the
projection-table lookup being con-leche's `hasProj` at the environment the
index answers for. -/
theorem majorsFlagsCheck_run {env : Env} {fe : IFEnv} {s : AState} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} {f0 : IndFlags} (hok : StateOK s) (hfe : IFEnvOK env fe s)
    (hp : dShape s.store p = some pP) :
    ∀ (Ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor) (s' : AState) (r : Unit),
      Ms.mapM (dMajor s.store) = some MsP →
      Arena.majorsFlagsCheck p f0 fe Ms s = .ok (r, s') →
      s' = s ∧ ∀ M ∈ MsP, M.member.isNone = true →
        (pP.isProp && (match M.ctors with | [c] => c.2 == 0 | _ => false)) = false ∧
        (f0.isImpredicative && (env.findTable? M.ind).isSome) = false
  | [], MsP, s', r, hMs, hrun => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hMs
    subst hMs
    simp only [Arena.majorsFlagsCheck] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, fun _ h => nomatch h⟩
  | M :: Ms, MsP, s', r, hMs, hrun => by
    obtain ⟨MP, MsP', rfl, hM, hMs'⟩ := mapM_option_cons_inv hMs
    obtain ⟨hind, -, -, -, -, hctors, hmem, -, -⟩ := dMajor_inv hM
    have hip := (dShape_inv hp).2.2.2.2.2.2
    simp only [Arena.majorsFlagsCheck] at hrun
    cases hmM : M.member with
    | some t =>
      rw [hmM] at hrun
      obtain ⟨rfl, ih⟩ := majorsFlagsCheck_run hok hfe hp Ms MsP' s' r hMs' hrun
      refine ⟨rfl, fun N hN hn => ?_⟩
      rcases List.mem_cons.mp hN with rfl | hN
      · rw [← hmem, hmM] at hn; exact nomatch hn
      · exact ih N hN hn
    | none =>
      rw [hmM] at hrun
      dsimp only at hrun
      obtain ⟨h1, hrun⟩ := AM.ite_fail_ok hrun
      have hT := IFEnvOK.findTable_isSome hok hfe hind
      have e1 : (pP.isProp && (match MP.ctors with | [c] => c.2 == 0 | _ => false)) = false := by
        rw [← hip]
        rcases dCtors_shape hctors with ⟨hc, hcP⟩ | ⟨c, cP, hc, hcP, hc2⟩ |
            ⟨c, d, r', cP, dP, rP, hc, hcP⟩
        · rw [hcP]; simp
        · rw [hc] at h1; simp only [hcP, hc2]; exact h1
        · rw [hcP]; simp
      cases hi : f0.isImpredicative with
      | false =>
        rw [hi] at hrun
        simp only [Bool.false_eq_true, ↓reduceIte] at hrun
        obtain ⟨rfl, ih⟩ := majorsFlagsCheck_run hok hfe hp Ms MsP' s' r hMs' hrun
        refine ⟨rfl, fun N hN hn => ?_⟩
        rcases List.mem_cons.mp hN with rfl | hN
        · exact ⟨e1, by simp⟩
        · simpa [hi] using ih N hN hn
      | true =>
        rw [hi] at hrun
        simp only [↓reduceIte] at hrun
        cases hft : fe.findTable? M.ind with
        | some _ =>
          rw [hft] at hrun
          exact absurd hrun (fun h => AM.fail_ok h)
        | none =>
          rw [hft] at hrun
          dsimp only at hrun
          obtain ⟨rfl, ih⟩ := majorsFlagsCheck_run hok hfe hp Ms MsP' s' r hMs' hrun
          refine ⟨rfl, fun N hN hn => ?_⟩
          rcases List.mem_cons.mp hN with rfl | hN
          · refine ⟨e1, ?_⟩
            rw [hft] at hT
            simp only [Bool.true_and]
            exact hT.symm
          · simpa [hi] using ih N hN hn

/-- con-leche: ConLeche/Kernel/Inductives/StreamRecs.lean:237-288 blockFlagsCheck
**The block's declared flags, validated**: where the twin passes, con-leche's
pure check passes at the environment the index answers for (`hasProj` its
projection tables); a pure step. -/
theorem blockFlagsCheck_run {env : Env} {fe : IFEnv} {s s' : AState} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} {isRec : Bool} {Ms : List Arena.TargetMajor}
    {MsP : List ConLeche.TargetMajor} {r : Unit} (hok : StateOK s)
    (hrl : ReadLCacheOK s.caches.readLC s.store) (hfe : IFEnvOK env fe s)
    (hp : dShape s.store p = some pP) (hMs : Ms.mapM (dMajor s.store) = some MsP)
    (hrun : Arena.blockFlagsCheck p isRec Ms fe s = .ok (r, s')) :
    PStep s s' ∧
      ConLeche.blockFlagsCheck pP isRec MsP (fun n => (env.findTable? n).isSome) = .ok () := by
  have hfl := dShape_flags hp
  have hk := BlockShape.k_spec hp
  obtain ⟨hms, -, -, -, -, hlg, hip⟩ := dShape_inv hp
  unfold Arena.blockFlagsCheck at hrun
  unfold ConLeche.blockFlagsCheck
  rw [← hfl]
  cases hf : p.flags with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | some fl =>
    rw [hf] at hrun
    dsimp only at hrun
    obtain ⟨c1, hrun⟩ := AM.ite_fail_ok hrun
    obtain ⟨c2, hrun⟩ := AM.ite_fail_ok hrun
    obtain ⟨c3, hrun⟩ := AM.ite_fail_ok hrun
    obtain ⟨c4, hrun⟩ := AM.ite_fail_ok hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hb⟩ := largeElimFlagOk_run hok hrl hp k1
    obtain ⟨c5, z1⟩ := AM.ite_fail_ok z1
    obtain ⟨u, s₂, k2, z2⟩ := AM.bind_ok z1
    have hp1 := dShape_ext p1.ext _ _ hp
    obtain ⟨e2, hM⟩ := membersFlagsCheck_run hp1 0 p.members pP.members fl s₁ s₂ u
      (dMember_ext.list p1.ext _ _ hms) k2
    rw [e2] at z2
    obtain ⟨e3, hMj⟩ := majorsFlagsCheck_run p1.ok (hfe.mono p1.ext) hp1 Ms MsP s' r
      (dMajor_ext.list p1.ext _ _ hMs) z2
    subst e3
    refine ⟨p1, ?_⟩
    rw [← hk, ← hlg, ← hip]
    have hb' : b = true := by simpa using c5
    rw [hb'] at hb
    simp only [bne, Bool.not_eq_false', beq_iff_eq] at c1
    simp only [Bool.not_eq_false'] at c2
    have hc4 : ((fl.headD default).hasLargeElim == p.large) = true := by
      simpa [bne] using c4
    have hc5 : ((fl.headD default).hasLargeElim &&
        !(!(fl.headD default).isImpredicative && (pP.resSort.isNeverZero ||
          (p.k == 1 && (pP.numCtors == 0 ||
            (pP.numCtors == 1 && ((fl.headD default).hasEta || (fl.headD default).isK))))))) = false := by
      rw [hk]
      cases hL : (fl.headD default).hasLargeElim
      · rfl
      · rw [hL] at hb
        simp only [Bool.not_true, Bool.false_or] at hb
        rw [← hb]; rfl
    simp only [c1, c2, c3, hc4, hc5, hM, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true,
      bind, Except.bind, pure, Except.pure]
    clear hrun k1 z1 z2 hMs
    rw [← hip] at hMj
    induction MsP with
    | nil => rfl
    | cons M Ms' ih =>
      have hM := hMj M List.mem_cons_self
      have ih' := ih (fun N hN hn => hMj N (List.mem_cons_of_mem _ hN) hn)
      simp only [List.forIn_cons]
      cases hn : M.member.isNone with
      | false =>
        simp only [hn, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure,
          Except.pure]
        exact ih'
      | true =>
        obtain ⟨a, b⟩ := hM hn
        rcases hc : M.ctors with _ | ⟨c, _ | ⟨d, r⟩⟩ <;> rw [hc] at a <;>
          simp only [Bool.and_false, Bool.and_true] at a <;>
          simp only [hn, hc, a, b, Bool.true_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
            bind, Except.bind, pure, Except.pure] <;>
          exact ih'

end ConRon.Bridge.Inductives
