/-
# `ConRon.Bridge.Modular.Flags` — the reach's inferred flags, Theorem 1 (task #166)

Upstream's worker facts ask the reach's flag inference only to be sound (`FlagsOk`,
`Verify/Driver/PropPart.lean`): `WorkerFacts.reach` is `∃ fl, FlagsOk fl ∧ CanGive (reachWith fl …)`.
con-ron runs its inference after the worker's freeze (`Arena/Modular/Reach.lean` `inferFlags`,
each statement at the frozen index's view of the part of the context below its name), so the
inference it supplies upstream is the one that accepts exactly when every recorded statement
resolves and is a proposition over that part (`soundFlags`, sound by definition:
`soundFlags_ok`), and the twin's accept is that condition (`inferFlags_run`).

The run style of `Bridge/Checker/Pooled.lean`'s `job_spec`: each statement in its own scratch
bracket, at `FoldOK` of the view (`view_foldOK'`), its inference `KnotSpec.infer`, its sort
`EnsureSortSpec`, the level test `lvlEq?_spec` — `checkThmVal_bridge`'s is-a-proposition test.
-/
module

public import ConRon.Bridge.Modular.ReachValid
public import ConRon.Bridge.Checker.Pooled
public import ConLeche.Verify.Driver.PropPart
import ConRon.Bridge.Stages
import ConRon.Bridge.Checker.DeclVal
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Names
import ConLeche.Verify.BridgeDecl
import Std.Data.HashMap.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean ConRon.Bridge.Inductives

/-! ## The inference con-ron supplies -/

/-- con-leche: ConLeche/Driver/Reach.lean:935 FlagInfer — **the sound flag inference**: it
accepts exactly when every recorded statement resolves and is a proposition over the part of
the context below its name, the condition upstream's `FlagsOk` asks of an accept. -/
noncomputable def soundFlags : ConLeche.Driver.FlagInfer := fun ctx ps =>
  open Classical in
  if ∀ p ∈ ps, p.2.2.type.constsResolve (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) = true ∧
      ConLeche.Modular.TypeIsProp .verified (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) p.2.2.type
  then .ok () else .error (.internal "a recorded statement is not a proposition below its name")

/-- con-leche: ConLeche/Verify/Driver/PropPart.lean:130 FlagsOk — `soundFlags` is sound. -/
theorem soundFlags_ok : ConLeche.Driver.FlagsOk soundFlags := by
  intro ctx _ ps h w y cv hm
  unfold soundFlags at h
  split at h
  · next hc => exact hc (w, y, cv) hm
  · cases h

/-- `soundFlags` accepts where every statement holds its condition. -/
theorem soundFlags_of {ctx : List Declaration} {ps : List (String × ConLeche.Name × ConstantVal)}
    (h : ∀ p ∈ ps, p.2.2.type.constsResolve (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) = true ∧
      ConLeche.Modular.TypeIsProp .verified (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) p.2.2.type) :
    soundFlags ctx ps = .ok () := by
  unfold soundFlags
  split
  · rfl
  · next hn => exact absurd h hn

/-! ## Each name's first record -/

/-- con-leche: ConLeche/Driver/Reach.lean:845-848 ctxPart — upstream's side of the twin's
`firstOwner`: each name's first record from position `j`. -/
@[expose] def firstOwnerC : List Declaration → Nat → Std.HashMap ConLeche.Name Nat →
    Std.HashMap ConLeche.Name Nat
  | [], _, m => m
  | d :: ds, j, m => firstOwnerC ds (j + 1)
      ((ConLeche.Modular.declNames d).foldl (fun m n => if m.contains n then m else m.insert n j) m)

theorem firstStep_get (j : Nat) (y : ConLeche.Name) :
    ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat),
      (ns.foldl (fun m n => if m.contains n then m else m.insert n j) m)[y]? =
        (m[y]?).or (if ns.contains y then some j else none)
  | [], m => by simp
  | n :: ns, m => by
    rw [List.foldl_cons, firstStep_get j y ns]
    cases hm : m[y]? with
    | some v =>
      have hc : m.contains y = true := by rw [Std.HashMap.contains_eq_isSome_getElem?, hm]; rfl
      split
      · rw [hm]; rfl
      · next hn =>
        have hne : n ≠ y := fun he => by subst he; exact hn hc
        simp [Std.HashMap.getElem?_insert, hne, hm]
    | none =>
      have hc : m.contains y = false := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, hm]; rfl
      simp only [Option.none_or, List.contains_cons]
      split
      · next hn =>
        have hne : n ≠ y := fun he => by subst he; rw [hn] at hc; cases hc
        rw [hm]
        have : (y == n) = false := by simpa [beq_eq_false_iff_ne] using Ne.symm hne
        simp [this]
      · next hn =>
        rw [Std.HashMap.getElem?_insert]
        by_cases he : n = y
        · subst he; simp
        · have h1 : (n == y) = false := by simpa [beq_eq_false_iff_ne] using he
          have h2 : (y == n) = false := by simpa [beq_eq_false_iff_ne] using Ne.symm he
          simp [h1, h2, hm]

theorem firstOwnerC_get (y : ConLeche.Name) :
    ∀ (ds : List Declaration) (j : Nat) (m : Std.HashMap ConLeche.Name Nat),
      (firstOwnerC ds j m)[y]? =
        (m[y]?).or (if ds.any (fun d => (ConLeche.Modular.declNames d).contains y) then
            some (j + ds.findIdx (fun d => (ConLeche.Modular.declNames d).contains y))
          else none)
  | [], j, m => by simp [firstOwnerC]
  | d :: ds, j, m => by
    rw [firstOwnerC, firstOwnerC_get y ds (j + 1), firstStep_get j y]
    simp only [List.any_cons, List.findIdx_cons]
    cases m[y]? with
    | some v => rfl
    | none =>
      simp only [Option.none_or]
      cases hd : (ConLeche.Modular.declNames d).contains y with
      | true => simp
      | false =>
        simp only [Option.none_or, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        split <;> simp; omega

/-- The first record storing `y`, or the length: the end of `ctxPart`. -/
theorem firstOwnerC_getD (ds : List Declaration) (y : ConLeche.Name) :
    ((firstOwnerC ds 0 {})[y]?).getD ds.length =
      ds.findIdx (fun d => (ConLeche.Modular.declNames d).contains y) := by
  rw [firstOwnerC_get]
  simp only [Std.HashMap.getElem?_empty, Option.none_or, Nat.zero_add]
  split
  · rfl
  · next h =>
    simp only [Bool.not_eq_true, List.any_eq_false] at h
    simp only [Option.getD_none]
    exact (List.findIdx_eq_length.mpr (fun d hd => by simpa using h d hd)).symm

/-! ## One statement -/

/-- con-leche: ConLeche/Verify/Driver/PropPart.lean:44 typeIsPropC_sound — **the twin's
is-a-proposition test answering `true` is `TypeIsProp`**, at the environment the index view
denotes: the inference, the sort, the pinned zero and the level verdict, as
`checkThmVal_bridge`'s test. -/
theorem typeIsPropC_run {env : Env} {fe : IFEnv} {cv : ConRon.Arena.Frontend.Olean.StmtRec}
    {c : ConstantVal} {s s' : AState} (hk : CoreSpec Arena.checkFuel) (hok : FoldOK env fe s)
    (hcv : denoteStmt s.store cv = some c) (hfv : c.type.hasFvar = false)
    (h : ConRon.Arena.Modular.typeIsPropC fe cv s = .ok (true, s')) :
    CheckOK false env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ConLeche.Modular.TypeIsProp .verified env c.type := by
  have hknot := hk.knot env fe hok.envWF
  have hsortS := hk.sort env fe hok.envWF
  have hwsty : ConLeche.Expr.WScoped 0 c.type := ConLeche.Expr.WScoped.of_not_hasFvar hfv
  have hty0 : denoteE s.store cv.type = some c.type := by
    simp only [denoteStmt] at hcv
    cases h1 : denoteN s.store.ns cv.name <;> cases h2 : cv.levelParams.mapM (denoteN s.store.ns) <;>
      cases h3 : denoteE s.store cv.type <;> simp_all
    cases hcv; rfl
  simp only [ConRon.Arena.Modular.typeIsPropC, Arena.zeroLevel] at h
  obtain ⟨stype, s1, ga, ra⟩ := AM.bind_ok h
  obtain ⟨hcka, hxa, hpa, hsima⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => CheckOK false env fe t ∧ Ext s.store t.store ∧ t.pins = s.pins ∧
      Core.SimE (ConLeche.inferTypeCore .verified false env) 0 c.type t.store r)
    rfl ga (hknot.infer s 0 cv.type c.type hok.check hty0 hwsty)
  obtain ⟨sty, hsty, hwssty, Fa, hFa⟩ := hsima
  obtain ⟨u, s2, gb, rb⟩ := AM.bind_ok ra
  obtain ⟨hckb, hxb, hpb, hsimb⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => CheckOK false env fe t ∧ Ext s1.store t.store ∧ t.pins = s1.pins ∧
      SimL (ConLeche.ensureSortCore .verified false env) 0 sty t.store r)
    rfl gb (hsortS s1 0 stype sty hcka hsty hwssty)
  obtain ⟨uu, huu, Fb, hFb⟩ := hsimb
  obtain ⟨z, s3, gc, rc⟩ := AM.bind_ok rb
  obtain ⟨hs3, hz⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => t = s2 ∧ denoteL s2.store.ls r = some .zero)
    rfl gc (pinZeroLevel_spec s2 hckb.pins)
  rw [hs3] at rc
  obtain ⟨o, s4, gd, rd⟩ := AM.bind_ok rc
  obtain ⟨hckd, hstd, hpd, lu, lv, hlu, hlv, hod⟩ := AM.of_run
    (P := fun t => t = s2)
    (Q := fun r t => CheckOK false env fe t ∧ t.store = s2.store ∧
      t.pins = s2.pins ∧ ∃ lu lv, denoteL s2.store.ls u = some lu ∧
        denoteL s2.store.ls z = some lv ∧ r = ConLeche.Level.isEquiv lu lv)
    rfl gd (Core.lvlEq?_spec s2 u z hckb)
  rw [Option.some.inj (hlu.symm.trans huu), Option.some.inj (hlv.symm.trans hz)] at hod
  cases o with
  | none => exact absurd rd (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  | some bb =>
  obtain ⟨hbb, rfl⟩ := AM.pure_ok rd
  refine ⟨hckd, by rw [hstd]; exact hxa.trans hxb, by rw [hpd, hpb, hpa], ?_⟩
  refine ⟨max Fa Fb, sty, uu, ConLeche.inferTypeCore_mono (Nat.le_max_left _ _) hFa,
    ConLeche.ensureSortCore_mono (Nat.le_max_right _ _) hFb, ?_⟩
  rw [← hod, hbb]

theorem denoteStmt_parts3 {st : EStore} {cv : ConRon.Arena.Frontend.Olean.StmtRec} {c : ConstantVal}
    (h : denoteStmt st cv = some c) :
    Frontend.denoteNList st.ns cv.levelParams = some c.levelParams ∧
      denoteE st cv.type = some c.type ∧ denoteN st.ns cv.name = some c.name := by
  simp only [denoteStmt] at h
  cases h1 : denoteN st.ns cv.name <;> cases h2 : cv.levelParams.mapM (denoteN st.ns) <;>
    cases h3 : denoteE st cv.type <;> simp_all
  cases h
  refine ⟨?_, rfl, rfl⟩
  rw [denoteNList_eq_mapM, h2]

/-- con-leche: ConLeche/Driver/Reach.lean:850-865 inferFlags — **one recorded statement
inferred**: its syntactic clauses, its resolution and `TypeIsProp`, at the environment `env`
the view denotes. -/
theorem inferOne_run {env : Env} {fe : IFEnv} {what : String} {y : NIdx}
    {cv : ConRon.Arena.Frontend.Olean.StmtRec} {c : ConstantVal} {s s' : AState}
    (hk : CoreSpec Arena.checkFuel) (hok : FoldOK env fe s)
    (hcv : denoteStmt s.store cv = some c)
    (h : ConRon.Arena.Modular.inferOne fe what y cv s = .ok ((), s')) :
    CheckOK false env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      c.type.constsResolve env = true ∧ ConLeche.Modular.TypeIsProp .verified env c.type := by
  obtain ⟨hl, ht, -⟩ := denoteStmt_parts3 hcv
  unfold ConRon.Arena.Modular.inferOne at h
  generalize hE : ConRon.Arena.Modular.exprOk cv.levelParams 0 cv.type = E at h
  generalize hR : ConRon.Arena.constsResolveFFast fe cv.type = R at h
  generalize hT : ConRon.Arena.Modular.typeIsPropC fe cv = T at h
  obtain ⟨eb, s2, k3, k4⟩ := AM.bind_ok h
  rw [← hE] at k3
  obtain ⟨e2, c2, p2, hb⟩ := exprOk_run hok.check.state hl ht k3
  have hok2 : FoldOK env fe s2 :=
    hok.step (hok.check.mono ⟨by rw [e2]; exact hok.check.state.wf⟩ (by rw [e2]; exact Ext.refl _)
      c2 p2) p2
  cases eb with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at k4
    obtain ⟨b, s1, k5, k6⟩ := AM.bind_ok k4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k5
    simp only [Bool.not_false, ↓reduceIte] at k6
    obtain ⟨_, _, _, k⟩ := AM.bind_ok k6
    first
      | exact absurd k fail_not_ok
      | (obtain ⟨_, _, k', _⟩ := AM.bind_ok k; exact absurd k' fail_not_ok)
  | true =>
  have hfv : c.type.hasFvar = false := by
    have : ConLeche.Driver.exprOk c.levelParams 0 c.type = true := hb.symm
    simp only [ConLeche.Driver.exprOk, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1.1
  simp only [↓reduceIte] at k4
  obtain ⟨b, s1, k5, k2⟩ := AM.bind_ok k4
  rw [← hR] at k5
  obtain ⟨e3, c3, p3, hr⟩ := constsResolveFFast_run hok2.check (by rw [e2]; exact ht) k5
  have hok3 : FoldOK env fe s1 :=
    hok2.step (hok2.check.mono ⟨by rw [e3]; exact hok2.check.state.wf⟩
      (by rw [e3]; exact Ext.refl _) c3 p3) p3
  cases b with
  | false =>
    simp only [Bool.not_false, ↓reduceIte] at k2
    obtain ⟨_, _, _, k⟩ := AM.bind_ok k2
    first
      | exact absurd k fail_not_ok
      | (obtain ⟨_, _, k', _⟩ := AM.bind_ok k; exact absurd k' fail_not_ok)
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at k2
  obtain ⟨bp, s5, k7, k6⟩ := AM.bind_ok k2
  rw [← hT] at k7
  cases bp with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at k6
    obtain ⟨_, _, _, k⟩ := AM.bind_ok k6
    first
      | exact absurd k fail_not_ok
      | (obtain ⟨_, _, k', _⟩ := AM.bind_ok k; exact absurd k' fail_not_ok)
  | true =>
  simp only [↓reduceIte] at k6
  obtain ⟨-, rfl⟩ := AM.pure_ok k6
  have hcv1 : denoteStmt s1.store cv = some c := by rw [e3, e2]; exact hcv
  obtain ⟨hck5, hx5, hp5, hprop⟩ := typeIsPropC_run hk hok3 hcv1 hfv k7
  refine ⟨hck5, by rw [e3, e2] at hx5; exact hx5, by rw [hp5, p3, p2], hr.symm, hprop⟩

/-- con-leche: ConLeche/Verify/Cached/StreamIndex.lean:461 jobs_run_from — `view_foldOK`, at
a position up to the records' count (the view of the whole stream too). -/
theorem view_foldOK'
    {dsP : List Declaration} {I : IStreamIndex} {s₁ s : AState}
    {k : Nat} (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁)
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex dsP.toArray))
    (hpI : PersIFBase I.base) (hk : k ≤ dsP.length)
    (hwf : ConLeche.EnvWF (ConLeche.streamEnv (dsP.take k)))
    (hnd : ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup)
    (hst : StateOK s) (hx : PExt s₁.store s.store)
    (hc : CacheOK false (ConLeche.streamEnv (dsP.take k)) s) (hp : s.pins = s₁.pins) :
    FoldOK (ConLeche.streamEnv (dsP.take k)) (I.view k) s := by
  have hIj := hI.pmono hpI hx
  have hspec : ConLeche.Cached.IndexSpec (dsP.take k ++ dsP.drop k)
      (ConLeche.Cached.buildIndex dsP.toArray) := by
    rw [List.take_append_drop]
    simpa using ConLeche.Cached.buildIndex_spec dsP.toArray
  have hlen : (dsP.take k).length = k := by simp; omega
  obtain ⟨hienv, hgate⟩ := view_ok hst hIj hspec hnd
  rw [hlen] at hienv hgate
  exact
    { check := ⟨hst, hc, hpinsOK.pmono hpersPins hx hp, hienv⟩
      envWF := hwf
      tblShape := fun t ht => by simp [IStreamIndex.view] at ht
      persPins := hpersPins.mono hp
      coh := ⟨fun _ => rfl, fun _ => rfl⟩
      gate := hgate }

/-! ## The statements, each in its bracket -/

/-- A statement denoting on a closed store denotes past a persistent extension. -/
theorem denoteStmt_pext {st st' : EStore} (hwf : StoreWF st) (hoff : st.scratchOn = false)
    (hx : PExt st st') {cv : ConRon.Arena.Frontend.Olean.StmtRec} {c : ConstantVal}
    (h : denoteStmt st cv = some c) : denoteStmt st' cv = some c := by
  obtain ⟨hl, ht, hn⟩ := denoteStmt_parts3 h
  have hl' := denoteNList_pext hx _ _ (Frontend.PersNList_of_denote hwf hoff hl) hl
  have hn' := denoteN_pext hx (Frontend.PersN_of_denote hwf hoff hn) hn
  have ht' := denoteE_pext hx (Frontend.PersE_of_denote hwf hoff ht) ht
  rw [denoteNList_eq_mapM] at hl'
  simp [denoteStmt, hn', hl', ht']

/-- A driver's state with empty caches at the run's pins is a `DriverOK` one. -/
theorem driverOK_of_worker {s₁ w : AState} (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁)
    (hw : WorkerOK s₁ w) : DriverOK w :=
  DriverOK.start hw.state (hpinsOK.pmono hpersPins hw.pext hw.pins) (CacheOK.of_empty hw.caches)

section Infer

variable {s₁ : AState} {I : IStreamIndex} {ctxC ownC : List Declaration}
  (hk : CoreSpec Arena.checkFuel)
  (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁) (hwf₁ : StoreWF s₁.store)
  (hoff₁ : s₁.store.scratchOn = false)
  (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex (ctxC ++ ownC).toArray))
  (hpI : PersIFBase I.base)
  (hpre : ∀ k ≤ ctxC.length, ConLeche.EnvWF (ConLeche.streamEnv (ctxC.take k)) ∧
    ((ConLeche.Cached.recsConsts (ctxC.take k)).map (·.name)).Nodup)
include hk hpinsOK hpersPins hwf₁ hoff₁ hI hpI hpre

/-- con-leche: ConLeche/Driver/Reach.lean:850-865 inferFlags — **the recorded statements,
each inferred in its own bracket** at the view of the part of the context below its name: each
resolves and is `TypeIsProp` there, and the worker's state stays a worker's. -/
theorem inferAll_run {owner : Std.HashMap NIdx Nat} {n : Nat}
    (hpos : ∀ (y : NIdx) (yC : ConLeche.Name), denoteN s₁.store.ns y = some yC →
      ConRon.Arena.Modular.partPos owner n y =
        ctxC.findIdx (fun d => (ConLeche.Modular.declNames d).contains yC)) :
    ∀ {ps : List (String × NIdx × ConRon.Arena.Frontend.Olean.StmtRec)}
      {psC : List (String × ConLeche.Name × ConstantVal)} {w w' : AState},
      WorkerOK s₁ w → ListRel (PendRel s₁.store) ps psC →
      ConRon.Arena.Modular.inferAll I owner n ps w = .ok ((), w') →
      WorkerOK s₁ w' ∧ ∀ p ∈ psC,
        p.2.2.type.constsResolve (streamEnv (ConLeche.Driver.ctxPart ctxC p.2.1)) = true ∧
        ConLeche.Modular.TypeIsProp .verified (streamEnv (ConLeche.Driver.ctxPart ctxC p.2.1))
          p.2.2.type
  | [], psC, w, w', hw, hps, h => by
    cases hps
    simp only [ConRon.Arena.Modular.inferAll] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨hw, fun _ h => nomatch h⟩
  | (what, y, cv) :: ps, _, w, w', hw, .cons (b := (what', yC, cvC)) ⟨hy, hcv⟩ hps, h => by
    simp only at hy hcv
    simp only [ConRon.Arena.Modular.inferAll, Bind.bind, StateT.bind, Except.bind] at h
    have henter : enterScratch w =
        .ok ((), AState.mk w.store.enableScratch Memos.empty w.caches w.pins) := rfl
    generalize hsj : AState.mk w.store.enableScratch Memos.empty w.caches w.pins = sj at henter
    rw [henter] at h
    simp only at h
    generalize hk' : ConRon.Arena.Modular.partPos owner n y = k at h
    have hkk : k = ctxC.findIdx (fun d => (ConLeche.Modular.declNames d).contains yC) := by
      rw [← hk', hpos y yC hy]
    have hkle : k ≤ ctxC.length := by rw [hkk]; exact List.findIdx_le_length
    have htake : (ctxC ++ ownC).take k = ctxC.take k := List.take_append_of_le_length hkle
    cases hone : ConRon.Arena.Modular.inferOne (I.view k) what y cv sj with
    | error e => rw [hone] at h; exact nomatch h
    | ok r =>
      obtain ⟨u, s'⟩ := r
      rw [hone] at h
      simp only at h
      have hdrop : dropScratch s' =
          .ok ((), AState.mk s'.store.dropScratch s'.memos Caches.empty s'.pins) := rfl
      rw [hdrop] at h
      simp only at h
      have hxj : PExt s₁.store sj.store := by
        rw [← hsj]; exact hw.pext.trans (PExt.enterScratch hw.state.wf)
      have hstj : StateOK sj := by rw [← hsj]; exact ⟨EStore.enableScratch_wf hw.state.wf⟩
      have hpj : sj.pins = s₁.pins := by rw [← hsj]; exact hw.pins
      have hcj : sj.caches = Caches.empty := by rw [← hsj]; exact hw.caches
      obtain ⟨hwfk, hndk⟩ := hpre k hkle
      have hok := view_foldOK' (dsP := ctxC ++ ownC) hpinsOK hpersPins hI hpI
        (Nat.le_trans hkle (by simp)) (by rw [htake]; exact hwfk) (by rw [htake]; exact hndk) hstj hxj
        (CacheOK.of_empty hcj) hpj
      rw [htake] at hok
      obtain ⟨hck', hx', hp', hres, hprop⟩ :=
        inferOne_run hk hok (denoteStmt_pext hwf₁ hoff₁ hxj hcv) (by cases u; exact hone)
      have hw2 : WorkerOK s₁ (AState.mk s'.store.dropScratch s'.memos Caches.empty s'.pins) :=
        { state := ⟨EStore.dropScratch_wf hck'.state.wf⟩
          pext := (hxj.trans (PExt.of_ext hx')).trans (PExt.dropScratch hck'.state.wf)
          caches := rfl
          pins := hp'.trans hpj }
      obtain ⟨hw', hrest⟩ := inferAll_run hpos hw2 hps h
      refine ⟨hw', fun p hp => ?_⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [ConLeche.Driver.ctxPart, ← hkk]
        exact ⟨hres, hprop⟩
      · exact hrest p hp

end Infer

/-! ## The owner map, and the whole inference -/

/-- One record's names inserted where absent: related maps stay related. -/
theorem insertFirst_rel {st : EStore} (hw : NStoreWF st.ns) (j : Nat) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name) {M : Std.HashMap NIdx Nat}
      {MC : Std.HashMap ConLeche.Name Nat}, Frontend.denoteNList st.ns ns = some xs →
      HMRel (· = ·) st M MC →
      HMRel (· = ·) st (ns.foldl (fun m n => if m.contains n then m else m.insert n j) M)
        (xs.foldl (fun m y => if m.contains y then m else m.insert y j) MC)
  | [], xs, M, MC, h, hr => by
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; exact hr
  | n :: ns, xs, M, MC, h, hr => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN st.ns n with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : Frontend.denoteNList st.ns ns with
    | none => rw [h1, h2] at h; simp at h
    | some xs' =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    have hc : M.contains n = MC.contains x := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?,
        hr.get_eq hw h1]
    simp only [List.foldl_cons, hc]
    split
    · exact insertFirst_rel hw j ns xs' h2 hr
    · exact insertFirst_rel hw j ns xs' h2 (hr.insert hw h1 rfl)

theorem firstOwnerGo_run :
    ∀ (ds : List IDeclaration) (dsC : List Declaration) (j : Nat)
      (M : Std.HashMap NIdx Nat) (MC : Std.HashMap ConLeche.Name Nat)
      {s s' : AState} {r : Std.HashMap NIdx Nat × Nat},
      DriverOK s →
      denoteDecls s.store ds = some dsC → HMRel (· = ·) s.store M MC →
      ds.foldlM (m := AM) (fun (acc : Std.HashMap NIdx Nat × Nat) d => do
        let ns ← ConRon.Arena.Modular.declNames d
        pure (ns.foldl (fun m n => if m.contains n then m else m.insert n acc.2) acc.1,
          acc.2 + 1)) (M, j) s = .ok (r, s') →
      CStep s s' ∧ HMRel (· = ·) s'.store r.1 (firstOwnerC dsC j MC)
  | [], dsC, j, M, MC, s, s', r, hok, hd, hr, h => by
    simp only [denoteDecls, Option.some.injEq] at hd
    subst hd
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, hr⟩
  | d :: ds, dsC, j, M, MC, s, s', r, hok, hd, hr, h => by
    simp only [denoteDecls] at hd
    cases h1 : Frontend.denoteDecl s.store d with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : denoteDecls s.store ds with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [List.foldlM_cons] at h
    obtain ⟨acc, s₁, k1, k2⟩ := AM.bind_ok h
    obtain ⟨ns, s₂, k3, k4⟩ := AM.bind_ok k1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
    obtain ⟨c1, hns⟩ := declNames_cstep hok h1 k3
    have hw := nsWF_of_StateOK c1.ok.state
    have hr₁ := insertFirst_rel hw j ns _ hns (hr.ext c1.ext (fun _ _ h => h))
    obtain ⟨c2, hr₂⟩ := firstOwnerGo_run ds xs (j + 1) _ _ c1.ok
      (denoteDecls_ext c1.ext _ _ h2) hr₁ k2
    exact ⟨c1.trans c2, hr₂⟩

theorem firstOwner_run {s s' : AState} {ds : List IDeclaration} {dsC : List Declaration}
    {M : Std.HashMap NIdx Nat} (hok : DriverOK s) (hd : denoteDecls s.store ds = some dsC)
    (h : ConRon.Arena.Modular.firstOwner ds s = .ok (M, s')) :
    CStep s s' ∧ HMRel (· = ·) s'.store M (firstOwnerC dsC 0 {}) := by
  simp only [ConRon.Arena.Modular.firstOwner] at h
  obtain ⟨r, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  exact firstOwnerGo_run ds dsC 0 {} {} hok hd (HMRel.empty _ _) h1

theorem denoteDecls_pext' {st st' : EStore} (hx : PExt st st') :
    ∀ {ds : List IDeclaration} {dsC : List Declaration}, (∀ d ∈ ds, PersDecl d) →
      denoteDecls st ds = some dsC → denoteDecls st' ds = some dsC
  | [], dsC, _, h => h
  | d :: ds, dsC, hp, h => by
    simp only [denoteDecls] at h ⊢
    cases h1 : Frontend.denoteDecl st d with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : denoteDecls st ds with
    | none => rw [h1, h2] at h; simp at h
    | some xs =>
    rw [h1, h2] at h
    rw [denoteDecl_pext hx (hp d (List.mem_cons_self ..)) h1,
      denoteDecls_pext' hx (fun d hd => hp d (List.mem_cons_of_mem _ hd)) h2]
    exact h

/-- con-leche: ConLeche/Driver/Reach.lean:850-865 inferFlags — **THEOREM 1 OF THE INFERRED
FLAGS**: the twin's inference accepting, from a worker's state at the frozen index `I` of the
context's records followed by the own records, is `soundFlags` accepting the denoted context and
statements — the inference con-ron supplies to upstream's `WorkerFacts.reach`, sound by
`soundFlags_ok`.  `s₁` is the driver's state the index was built from (`buildIndex_run`'s);
`hpre`, every prefix of the context well formed with distinct names, is upstream's `worker_ctx`
of the context. -/
theorem inferFlags_run {s₁ : AState} {I : IStreamIndex} {ctxC ownC : List Declaration}
    (hk : CoreSpec Arena.checkFuel)
    (hpinsOK : PinsOK s₁) (hpersPins : PersPins s₁) (hwf₁ : StoreWF s₁.store)
    (hoff₁ : s₁.store.scratchOn = false)
    (hI : IndexDenotes s₁.store I (ConLeche.Cached.buildIndex (ctxC ++ ownC).toArray))
    (hpI : PersIFBase I.base)
    (hpre : ∀ k ≤ ctxC.length, ConLeche.EnvWF (ConLeche.streamEnv (ctxC.take k)) ∧
      ((ConLeche.Cached.recsConsts (ctxC.take k)).map (·.name)).Nodup)
    {ctx : Array IDeclaration} (hpd : ∀ d ∈ ctx.toList, PersDecl d)
    (hctx : denoteDecls s₁.store ctx.toList = some ctxC)
    {pending : Array (String × NIdx × ConRon.Arena.Frontend.Olean.StmtRec)}
    {pendC : List (String × ConLeche.Name × ConstantVal)}
    (hpend : ListRel (PendRel s₁.store) pending.toList pendC)
    {w w' : AState} (hw : WorkerOK s₁ w)
    (h : ConRon.Arena.Modular.inferFlags I ctx pending w = .ok ((), w')) :
    WorkerOK s₁ w' ∧ soundFlags ctxC pendC = .ok () := by
  unfold ConRon.Arena.Modular.inferFlags at h
  by_cases he : pending.isEmpty = true
  · simp only [he, ↓reduceIte] at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    have : pending.toList = [] := by simpa using he
    rw [this] at hpend
    cases hpend
    exact ⟨hw, soundFlags_of (fun _ h => nomatch h)⟩
  simp only [he, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
  simp only [Bind.bind, StateT.bind, Except.bind] at h
  have henter : enterScratch w =
      .ok ((), AState.mk w.store.enableScratch Memos.empty w.caches w.pins) := rfl
  generalize hsj : AState.mk w.store.enableScratch Memos.empty w.caches w.pins = sj at henter
  rw [henter] at h
  simp only at h
  have hxj : PExt s₁.store sj.store := by
    rw [← hsj]; exact hw.pext.trans (PExt.enterScratch hw.state.wf)
  have hwj : WorkerOK s₁ sj :=
    { state := by rw [← hsj]; exact ⟨EStore.enableScratch_wf hw.state.wf⟩
      pext := hxj
      caches := by rw [← hsj]; exact hw.caches
      pins := by rw [← hsj]; exact hw.pins }
  cases hfo : ConRon.Arena.Modular.firstOwner ctx.toList sj with
  | error e => rw [hfo] at h; exact nomatch h
  | ok r =>
    obtain ⟨owner, s'⟩ := r
    rw [hfo] at h
    simp only at h
    obtain ⟨c1, hown⟩ := firstOwner_run (driverOK_of_worker hpinsOK hpersPins hwj)
      (denoteDecls_pext' hxj hpd hctx) hfo
    have hdrop : dropScratch s' =
        .ok ((), AState.mk s'.store.dropScratch s'.memos Caches.empty s'.pins) := rfl
    rw [hdrop] at h
    simp only at h
    have hw2 : WorkerOK s₁ (AState.mk s'.store.dropScratch s'.memos Caches.empty s'.pins) :=
      { state := ⟨EStore.dropScratch_wf c1.ok.state.wf⟩
        pext := (hxj.trans (PExt.of_ext c1.ext)).trans (PExt.dropScratch c1.ok.state.wf)
        caches := rfl
        pins := c1.pins.trans hwj.pins }
    have hlen : ctx.size = ctxC.length := by simpa using denoteDecls_length hctx
    have hpos : ∀ (y : NIdx) (yC : ConLeche.Name), denoteN s₁.store.ns y = some yC →
        ConRon.Arena.Modular.partPos owner ctx.size y =
          ctxC.findIdx (fun d => (ConLeche.Modular.declNames d).contains yC) := by
      intro y yC hy
      have hy' : denoteN s'.store.ns y = some yC :=
        denoteN_ext (denoteN_pext hxj (Frontend.PersN_of_denote hwf₁ hoff₁ hy) hy) c1.ext
      simp only [ConRon.Arena.Modular.partPos]
      rw [hown.get_eq (nsWF_of_StateOK c1.ok.state) hy', hlen, firstOwnerC_getD]
    obtain ⟨hw', hall⟩ := inferAll_run hk hpinsOK hpersPins hwf₁ hoff₁ hI hpI hpre hpos hw2
      hpend h
    exact ⟨hw', soundFlags_of hall⟩

end ConRon.Bridge.Modular
