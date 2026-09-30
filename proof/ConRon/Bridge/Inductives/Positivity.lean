/-
# `ConRon.Bridge.Inductives.Positivity` — Theorem 1 for the positivity walk
(DESIGN.md §8.2, task #105)

`Arena/Inductives/Positivity.lean` against `ConLeche/Kernel/Inductives/
Positivity.lean`, everything `Bridge/Inductives/PosWalks.lean` (the pure leaf
walks) and `Bridge/Inductives/FieldTele.lean` (`closeTelescope`,
`instPisWith`) do not already cover: the container lookups, the instantiation's
former (`nestInstType`), the canonical crests, the frame's helpers, the ONE
mutual block (`nestFields`, `nestCtors`, `nestFrame`, `nestContNew`,
`nestContKey`, `nestCont`, `nestPos`), the member holes, the uniform-occurrence
check, the root frame and the seeds.

The TEMPLATE is con-leche's cached bridge `ConLeche/Verify/Cached/NestPosC.lean`:
the same induction (`nestPos` at `fuel + 1` from the frame lemmas at `fuel`),
the same scoping side conditions (`WScoped` of every knot call's argument,
`ConLeche/Verify/Inductives/NestScope.lean`), with handles DENOTING where the
template has `v = w`.  The walk calls the knot (`whnf`, `inferTypeCore`,
`ensureSortCore`), so the core-grade statements are `CSpecF` against the
monad-generic con-leche function run at `fueledOpsM μ`, related through
`Records.lean`'s denotations (`dCtx`, `dProg`, `dState`, `dKey`, `kindOf`).
The twin's deviations (its module note) are absorbed as follows:

* `prog` is outermost-first: `dProg` reverses, so a frame's holes APPENDED to
  the twin's stack are PREPENDED (reversed) to con-leche's;
* `nestCtors`' `root` flag and fuel stand for con-leche's continuation `rec`:
  `nestRecP` below is the continuation they denote;
* the accumulators (`nestFields`' `ks`/`nds`, `nestCtors`' `outs`,
  `nestRoot`'s `outs`, `nestGroupCtors`' `out`, `nestHoles.go`'s `out`) are the
  prefix of con-leche's result list;
* `NestState.ctorNfs` is an `Array` on both sides (`dState` reads `toList`).
-/
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.StructParts
import ConRon.Bridge.Checker.Base
import ConLeche.Verify.Cached.NestPosC

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option linter.unusedVariables false

open ConLeche ConRon.Arena ConRon.Bridge PW

/-! ## Run forms of the three knot calls -/

section Knot

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:27 CheckerOps.whnf — the knot's
`whnf` slot in run form, its answer an `FOk` of `fueledOpsM`'s. -/
theorem whnf_crun (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {s s' : AState} {d : Nat} {e r : EIdx} {eP : Expr}
    (hok : CheckOK μ env fe s) (he : denoteE s.store e = some eP)
    (hw : Expr.WScoped d eP)
    (hrun : Arena.whnf μ fe Arena.checkFuel d e s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧ ∃ w, denoteE s'.store r = some w ∧ Expr.WScoped d w ∧
      FOk ((fueledOpsM μ).whnf env d eP) w := by
  obtain ⟨h1, h2, h3, v, hv, hwv, hF⟩ := AM.of_run (P := fun u => u = s)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s.store u.store ∧ u.pins = s.pins ∧
      Core.SimE (ConLeche.whnf μ env) d eP u.store r)
    rfl hrun ((hk.knot env fe henv).whnf s d e eP hok he hw)
  exact ⟨⟨h1, h2, h3⟩, v, hv, hwv, FOk.whnf hF⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:27 CheckerOps.inferType — the
knot's `infer` slot in run form. -/
theorem infer_crun (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {s s' : AState} {d : Nat} {e r : EIdx} {eP : Expr}
    (hok : CheckOK μ env fe s) (he : denoteE s.store e = some eP)
    (hw : Expr.WScoped d eP)
    (hrun : Arena.inferTypeCore μ fe Arena.checkFuel d e s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧ ∃ w, denoteE s'.store r = some w ∧ Expr.WScoped d w ∧
      FOk ((fueledOpsM μ).inferType env d eP) w := by
  obtain ⟨h1, h2, h3, v, hv, hwv, hF⟩ := AM.of_run (P := fun u => u = s)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s.store u.store ∧ u.pins = s.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) d eP u.store r)
    rfl hrun ((hk.knot env fe henv).infer s d e eP hok he hw)
  exact ⟨⟨h1, h2, h3⟩, v, hv, hwv, FOk.inferType hF⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:27 CheckerOps.ensureSort — the
seventh entry point in run form. -/
theorem ensureSort_crun (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {s s' : AState} {d : Nat} {e : EIdx} {r : LIdx} {eP : Expr}
    (hok : CheckOK μ env fe s) (he : denoteE s.store e = some eP)
    (hw : Expr.WScoped d eP)
    (hrun : Arena.ensureSortCore μ fe Arena.checkFuel d e s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧ ∃ u, denoteL s'.store.ls r = some u ∧
      FOk ((fueledOpsM μ).ensureSort env d eP) u := by
  obtain ⟨h1, h2, h3, u, hu, hF⟩ := AM.of_run (P := fun u => u = s)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s.store u.store ∧ u.pins = s.pins ∧
      SimL (ConLeche.ensureSortCore μ env) d eP u.store r)
    rfl hrun (hk.sort env fe henv s d e eP hok he hw)
  exact ⟨⟨h1, h2, h3⟩, u, hu, FOk.ensureSort hF⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean instantiateLevelParams — the
executed level instantiation at the checking invariant (it writes the three
readback caches, so the frame is a `CoreStep`). -/
theorem instLPFast_cstep {s s' : AState}
    {ks : List NIdx} {us : LsIdx} {e r : EIdx} {ksv : List ConLeche.Name}
    {usv : List Level} {eP : Expr} (hok : CheckOK μ env fe s)
    (hks : Frontend.denoteNList s.store.ns ks = some ksv)
    (hus : denoteLs s.store.lss us = some usv) (he : denoteE s.store e = some eP)
    (hrun : Arena.instLPFast Arena.coreWalkFuel ks us e s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧
      denoteE s'.store r = some (eP.instantiateLevelParams ksv usv) := by
  obtain ⟨hst, hx, -, hL, hLs, hN, hc, hp, -, hrel⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun
    (ExprOps.instLPFast_spec _ s ks us e ksv usv hok.state hok.caches.readN hok.caches.readL
      hok.caches.readLs hks hus (by rw [he]; rfl))
  exact ⟨⟨Core.CheckOK.ofInstLP hok hst hx hL hLs hN hc hp, hx, hp⟩, hrel eP he⟩

end Knot

/-! ## Small run forms -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:201-204 unwrapOr — an
accepting `unwrapOr` had a value and moved nothing. -/
theorem unwrapOr_ok {α : Type} {o : Option α} {e : Arena.CheckError} {a : α}
    {s s' : AState} (h : Arena.unwrapOr o e s = .ok (a, s')) : o = some a ∧ s' = s := by
  cases o with
  | none => exact absurd h (fun hc => failOk hc)
  | some x =>
    simp only [Arena.unwrapOr] at h
    obtain ⟨rfl, rfl⟩ := pureOk h
    exact ⟨rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:197-199 liftFueled — an accepting
`liftFueled` had a value and moved nothing. -/
theorem liftFueled_ok {α : Type} {w : String} {o : Option α} {a : α}
    {s s' : AState} (h : Arena.liftFueled w o s = .ok (a, s')) : o = some a ∧ s' = s := by
  cases o with
  | none => exact absurd h (fun hc => failOk hc)
  | some x =>
    simp only [Arena.liftFueled] at h
    obtain ⟨rfl, rfl⟩ := pureOk h
    exact ⟨rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:201-204 unwrapOr — at `some`,
the pure side's `unwrapOr` is `pure`. -/
theorem FOk.unwrapOr {α : Type} {a : α} {e : ConLeche.CheckError} :
    FOk (ConLeche.unwrapOr (m := FueledM) (some a) e) a := FOk.pure a

/-- con-leche: ConLeche/Kernel/Core.lean:197-199 liftFueled — the same. -/
theorem FOk.liftFueled {α : Type} {a : α} {w : String} :
    FOk (ConLeche.liftFueled (m := FueledM) w (some a)) a := FOk.pure a

/-! ## The environment index, read at a denoting name -/

section Find

variable {env : Env} {fe : IFEnv}

/-- con-leche: none — an index HIT at a denoting handle is an environment hit,
at the constant's denotation. -/
theorem find_some_rel {s : AState} (hie : IFEnvOK env fe s) {n : NIdx}
    {nP : ConLeche.Name} (hn : denoteN s.store.ns n = some nP) {ci : IConstantInfo}
    (hf : fe.find? n = some ci) :
    ∃ c, Frontend.denoteCI s.store ci = some c ∧ env.find? nP = some c := by
  obtain ⟨nm, c, hnm, hc, he⟩ := hie.hit n ci hf
  rw [hn] at hnm
  obtain rfl := Option.some.inj hnm
  exact ⟨c, hc, he⟩

/-- con-leche: none — `denoteCI` keeps the constructor: an `.indInfo`. -/
theorem denoteCI_indInfo_inv {st : EStore} {cv : IConstantVal} {caps : IIndCaps}
    {c : ConstantInfo} (h : Frontend.denoteCI st (.indInfo cv caps) = some c) :
    ∃ cvP capsP, Frontend.denoteCV st cv = some cvP ∧
      Frontend.denoteCaps st caps = some capsP ∧ c = .indInfo cvP capsP := by
  simp only [Frontend.denoteCI] at h
  cases h1 : Frontend.denoteCV st cv with
  | none => rw [h1] at h; exact nomatch h
  | some cvP =>
  cases h2 : Frontend.denoteCaps st caps with
  | none => rw [h1, h2] at h; exact nomatch h
  | some capsP =>
  rw [h1, h2] at h
  exact ⟨cvP, capsP, rfl, rfl, (Option.some.inj h).symm⟩

/-- con-leche: none — `denoteCI` keeps the constructor: a `.ctorInfo`. -/
theorem denoteCI_ctorInfo_inv {st : EStore} {cv : IConstantVal} {a b : Nat}
    {c : ConstantInfo} (h : Frontend.denoteCI st (.ctorInfo cv a b) = some c) :
    ∃ cvP, Frontend.denoteCV st cv = some cvP ∧ c = .ctorInfo cvP a b := by
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  obtain ⟨cvP, h1, rfl⟩ := h
  exact ⟨cvP, h1, rfl⟩

end Find

/-! ## Containers: `nestCtorEntry`, `nestContainer` -/

/-- con-leche: none — a constructor entry's denotation. -/
def dCE (st : EStore) (x : IConstantVal × Nat × Nat) : Option (ConstantVal × Nat × Nat) :=
  (Frontend.denoteCV st x.1).map (·, x.2)

theorem dCE_ext : DExt dCE := by
  intro st st' hx x y h
  simp only [dCE, Option.map_eq_some_iff] at h ⊢
  obtain ⟨cv, hcv, rfl⟩ := h
  exact ⟨cv, denoteCV_ext hcv hx, rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:684-695 nestCtorEntry
A stored constant's entry as a constructor of `C`, exactly con-leche's. -/
theorem nestCtorEntry_spec (C : NIdx) (CP : ConLeche.Name) (ci : IConstantInfo)
    (c : ConstantInfo) :
    PSpec (fun st => denoteN st.ns C = some CP ∧ Frontend.denoteCI st ci = some c)
      (Arena.nestCtorEntry C ci)
      (ROp (fun y st x => dCE st x = some y) (ConLeche.nestCtorEntry CP c)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hC, hci⟩ := hp
  cases ci with
  | ctorInfo cv nPc nF =>
    obtain ⟨cvP, hcv, rfl⟩ := denoteCI_ctorInfo_inv hci
    obtain ⟨-, -, hty⟩ := denoteCV_inv hcv
    simp only [Arena.nestCtorEntry] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hty h1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      refine ⟨PStep.refl hok, ?_⟩
      show ConLeche.nestCtorEntry CP (.ctorInfo cvP nPc nF) = none
      simp only [ConLeche.nestCtorEntry, stripPis_none hbp]
    | some q =>
      obtain ⟨bs, body⟩ := q
      obtain ⟨xs, x, hsp, hbody⟩ := stripPis_some hbp
      dsimp only at h2
      obtain ⟨hd, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨rfl, hhd⟩ := getAppFn_run hok hbody h3
      by_cases htg : (hd.tag == ETag.const) = true
      · rw [if_pos htg] at h4
        obtain ⟨o, s₃, h5, h6⟩ := bindOk h4
        obtain ⟨rfl, ho⟩ := viewConst_run h5
        cases o with
        | none => exact absurd h6 (fun hc => failDanglingE_ok hc)
        | some p =>
          obtain ⟨n, us⟩ := p
          have hw := view_of_viewConst_tag htg ho.symm
          obtain ⟨nm, ls, hx, hn, hls⟩ := denote_const_inv hok.wf hw hhd
          dsimp only at h6
          have hb := beq_handle_eq hok.wf hn hC
          refine ⟨?_, ?_⟩
          · by_cases hc : (n == C) = true
            · rw [if_pos hc] at h6; obtain ⟨rfl, rfl⟩ := pureOk h6; exact PStep.refl hok
            · rw [if_neg hc] at h6; obtain ⟨rfl, rfl⟩ := pureOk h6; exact PStep.refl hok
          · simp only [ConLeche.nestCtorEntry, hsp, hx]
            by_cases hc : (n == C) = true
            · rw [if_pos hc] at h6
              obtain ⟨rfl, rfl⟩ := pureOk h6
              rw [hb] at hc
              simp only [hc, if_true]
              exact ⟨_, rfl, by simp [dCE, hcv]⟩
            · rw [if_neg hc] at h6
              obtain ⟨rfl, rfl⟩ := pureOk h6
              rw [hb] at hc
              simp only [hc]
              rfl
      · rw [if_neg htg] at h4
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨PStep.refl hok, ?_⟩
        show ConLeche.nestCtorEntry CP (.ctorInfo cvP nPc nF) = none
        simp only [ConLeche.nestCtorEntry, hsp]
        cases hg : x.getAppFn with
        | const c us =>
          rw [hg] at hhd
          exact absurd (tag_const_of_denote hok.wf hhd) (by simpa using htg)
        | _ => rfl
  | _ =>
    simp only [Arena.nestCtorEntry] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show ConLeche.nestCtorEntry CP c = none
    have := denoteCI_not_ctor hci (by intro v a b h; exact nomatch h)
    cases c with
    | ctorInfo v a b => exact absurd rfl (this v a b)
    | _ => rfl

/-- con-leche: none — the entry step of `nestContainer`'s `filterMapM`: a
missing name is no entry on both sides. -/
theorem nestCtorLookup_spec {env : Env} {fe : IFEnv} (C : NIdx) (CP : ConLeche.Name)
    (n : NIdx) (nP : ConLeche.Name) :
    PSpec (fun st => IFEnvOKS env fe st ∧ denoteN st.ns C = some CP ∧
        denoteN st.ns n = some nP)
      (match fe.find? n with
       | some ci => Arena.nestCtorEntry C ci
       | none => pure none)
      (ROp (fun y st x => dCE st x = some y) ((env.find? nP).bind (ConLeche.nestCtorEntry CP))) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hie, hC, hn⟩ := hp
  have hie' := hie s₀ rfl
  cases hf : fe.find? n with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show _ = none
    rw [hie'.miss hok hn hf]; rfl
  | some ci =>
    rw [hf] at hrun
    obtain ⟨c, hc, he⟩ := find_some_rel hie' hn hf
    rw [he, Option.bind_some]
    exact nestCtorEntry_spec C CP ci c s₀ s' r hok ⟨hC, hc⟩ hrun

/-- con-leche: none — `List.filterMapM`'s loop over the lookup step: the answer
is the accumulator reversed, then entries denoting con-leche's `filterMap`. -/
theorem nestCtorLoop_run {env : Env} {fe : IFEnv} (C : NIdx) (CP : ConLeche.Name) :
    ∀ (ns : List NIdx) (nsP : List ConLeche.Name) (acc : List (IConstantVal × Nat × Nat))
      (s₀ s' : AState) (r : List (IConstantVal × Nat × Nat)), StateOK s₀ →
      IFEnvOKS env fe s₀.store → denoteN s₀.store.ns C = some CP →
      Frontend.denoteNList s₀.store.ns ns = some nsP →
      List.filterMapM.loop (m := AM) (fun n => match fe.find? n with
          | some ci => Arena.nestCtorEntry C ci
          | none => pure none) ns acc s₀ = Except.ok (r, s') →
      PStep s₀ s' ∧ ∃ r', r = acc.reverse ++ r' ∧
        r'.mapM (dCE s'.store) = some (nsP.filterMap fun n =>
          (env.find? n).bind (ConLeche.nestCtorEntry CP)) := by
  intro ns
  induction ns with
  | nil =>
    intro nsP acc s₀ s' r hok _ _ hns hrun
    simp only [Frontend.denoteNList, Option.some.injEq] at hns
    subst hns
    simp only [List.filterMapM.loop] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], by simp, rfl⟩
  | cons a as ih =>
    intro nsP acc s₀ s' r hok hie hC hns hrun
    simp only [Frontend.denoteNList] at hns
    cases ha : denoteN s₀.store.ns a with
    | none => rw [ha] at hns; simp at hns
    | some aP =>
    cases has : Frontend.denoteNList s₀.store.ns as with
    | none => rw [ha, has] at hns; simp at hns
    | some asP =>
    rw [ha, has] at hns
    obtain rfl := (Option.some.inj hns).symm
    simp only [List.filterMapM.loop] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := nestCtorLookup_spec (fe := fe) C CP a aP s₀ s₁ o hok ⟨hie, hC, ha⟩ h1
    have hie1 := hie.mono p1.ext
    have hC1 := denoteN_ext hC p1.ext
    have has1 := denoteNListE_ext p1.ext _ _ has
    cases o with
    | none =>
      dsimp only at h2
      obtain ⟨p2, r', rfl, hr'⟩ := ih asP acc s₁ s' r p1.ok hie1 hC1 has1 h2
      refine ⟨p1.trans p2, r', rfl, ?_⟩
      simp only [ROp] at ho
      simp only [List.filterMap_cons, ho]
      exact hr'
    | some b =>
      dsimp only at h2
      obtain ⟨p2, r', rfl, hr'⟩ := ih asP (b :: acc) s₁ s' r p1.ok hie1 hC1 has1 h2
      obtain ⟨y, hy, hb⟩ := ho
      refine ⟨p1.trans p2, b :: r', by simp, ?_⟩
      simp only [List.filterMap_cons, hy, List.mapM_cons, Option.bind_eq_bind,
        Option.pure_def, dCE_ext p2.ext _ _ hb, hr', Option.bind_some]

/-- con-leche: none — a container's answer: its parameter count and its
constructors' records (`dCtors`). -/
abbrev RCont (q : Nat × List (ConstantVal × Nat)) :
    EStore → Nat × List (IConstantVal × Nat) → Prop :=
  fun st r => r.1 = q.1 ∧ dCtors st r.2 = some q.2

theorem dCtors_map_dCE {st : EStore} :
    ∀ {cs : List (IConstantVal × Nat × Nat)} {csP : List (ConstantVal × Nat × Nat)},
      cs.mapM (dCE st) = some csP →
      dCtors st (cs.map fun c => (c.1, c.2.2)) = some (csP.map fun c => (c.1, c.2.2)) := by
  intro cs
  induction cs with
  | nil => intro csP h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
           subst h; rfl
  | cons c cs ih =>
    intro csP h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hc : dCE st c with
    | none => rw [hc] at h; simp at h
    | some y =>
      cases hcs : cs.mapM (dCE st) with
      | none => rw [hc, hcs] at h; simp at h
      | some ys =>
        rw [hc, hcs] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [dCE, Option.map_eq_some_iff] at hc
        obtain ⟨cv, hcv, rfl⟩ := hc
        have := ih hcs
        simp only [dCtors, List.map_cons, List.mapM_cons, Option.bind_eq_bind,
          Option.pure_def] at this ⊢
        rw [this]
        simp [dCtor, hcv]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:697-712 nestContainer
The container's parameter count and constructors, exactly con-leche's at any
context reading the environment. -/
theorem nestContainer_spec {env : Env} {fe : IFEnv} (ctxP : ConLeche.NestCtx)
    (hfind : ctxP.find? = env.find?) (C : NIdx) (CP : ConLeche.Name) :
    PSpec (fun st => IFEnvOKS env fe st ∧ denoteN st.ns C = some CP)
      (Arena.nestContainer fe C) (ROp RCont (ConLeche.nestContainer ctxP CP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hie, hC⟩ := hp
  have hie' := hie s₀ rfl
  simp only [Arena.nestContainer] at hrun
  simp only [ConLeche.nestContainer, hfind]
  cases hf : fe.find? C with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show _ = none
    rw [hie'.miss hok hC hf]
  | some ci =>
    rw [hf] at hrun
    obtain ⟨c, hc, he⟩ := find_some_rel hie' hC hf
    rw [he]
    cases ci with
    | indInfo cv caps =>
      obtain ⟨cvP, capsP, -, hcaps, rfl⟩ := denoteCI_indInfo_inv hc
      dsimp only at hrun
      obtain ⟨cs, s₁, h1, h2⟩ := bindOk hrun
      have hctors : Frontend.denoteNList s₀.store.ns caps.ctors = some capsP.ctors := by
        simp only [Frontend.denoteCaps] at hcaps
        split at hcaps
        · rename_i ct all ctors _ _ hct
          obtain rfl := (Option.some.inj hcaps).symm
          exact hct
        · exact nomatch hcaps
      have hnp : caps.nparams = capsP.nparams := by
        simp only [Frontend.denoteCaps] at hcaps
        split at hcaps
        · obtain rfl := (Option.some.inj hcaps).symm; rfl
        · exact nomatch hcaps
      obtain ⟨p1, r', hr, hr'⟩ := nestCtorLoop_run (env := env) C CP caps.ctors capsP.ctors []
        s₀ s₁ cs hok hie hC hctors h1
      simp only [List.reverse_nil, List.nil_append] at hr
      subst hr
      dsimp only
      generalize List.filterMap _ capsP.ctors = csP at hr'
      cases cs with
      | nil =>
        obtain ⟨rfl, rfl⟩ := pureOk h2
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hr'
        subst hr'
        exact ⟨p1, _, rfl, hnp, rfl⟩
      | cons c0 rest =>
        obtain ⟨rfl, rfl⟩ := pureOk h2
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hr'
        cases hc0 : dCE s'.store c0 with
        | none => rw [hc0] at hr'; simp at hr'
        | some y =>
          cases hrs : rest.mapM (dCE s'.store) with
          | none => rw [hc0, hrs] at hr'; simp at hr'
          | some ys =>
            rw [hc0, hrs] at hr'
            simp only [Option.bind_some, Option.some.injEq] at hr'
            subst hr'
            have hy : c0.2 = y.2 := by
              simp only [dCE, Option.map_eq_some_iff] at hc0
              obtain ⟨_, _, rfl⟩ := hc0; rfl
            refine ⟨p1, _, rfl, by simp [hy], ?_⟩
            have := dCtors_map_dCE (st := s'.store) (cs := c0 :: rest) (csP := y :: ys)
              (by simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, hc0, hrs,
                Option.bind_some])
            exact this
    | _ =>
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show _ = none
      have := denoteCI_not_ind hc (by intro v caps h; exact nomatch h)
      cases c with
      | indInfo v k => exact absurd rfl (this v k)
      | _ => rfl

/-! ## The frame's environment readers: `nestBlockOf`, `nestFrameMates`,
`nestArity`, `nestGroupCtors` -/

/-- con-leche: ConLeche/Kernel/Env.lean:352-372 IndCaps — the capability
record's three fields the walk reads, denoted. -/
theorem denoteCaps_inv {st : EStore} {caps : IIndCaps} {capsP : IndCaps}
    (h : Frontend.denoteCaps st caps = some capsP) :
    Frontend.denoteNList st.ns caps.all = some capsP.all ∧
      Frontend.denoteNList st.ns caps.ctors = some capsP.ctors ∧
      caps.nparams = capsP.nparams := by
  simp only [Frontend.denoteCaps] at h
  split at h
  · rename_i ct all ctors _ hall hct
    obtain rfl := (Option.some.inj h).symm
    exact ⟨hall, hct, rfl⟩
  · exact nomatch h

/-- con-leche: none — `Option`'s `mapM` distributes over `++`. -/
theorem mapM_option_append {α β : Type} {f : α → Option β} :
    ∀ {xs ys : List α} {a b : List β}, xs.mapM f = some a → ys.mapM f = some b →
      (xs ++ ys).mapM f = some (a ++ b) := by
  intro xs
  induction xs with
  | nil =>
    intro ys a b ha hb
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at ha
    subst ha; simpa using hb
  | cons x xs ih =>
    intro ys a b ha hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at ha
    cases hx : f x with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : xs.mapM f with
      | none => rw [hx, hxs] at ha; simp at ha
      | some zs =>
        rw [hx, hxs] at ha
        simp only [Option.bind_some, Option.some.injEq] at ha
        subst ha
        simp only [List.cons_append, List.mapM_cons, Option.bind_eq_bind, Option.pure_def, hx,
          ih hxs hb, Option.bind_some]

/-- con-leche: none — a name-handle list denotes, appended. -/
theorem denoteNList_append {st : NStore} :
    ∀ {xs ys : List NIdx} {a b : List ConLeche.Name},
      Frontend.denoteNList st xs = some a → Frontend.denoteNList st ys = some b →
      Frontend.denoteNList st (xs ++ ys) = some (a ++ b) := by
  intro xs
  induction xs with
  | nil =>
    intro ys a b ha hb
    simp only [Frontend.denoteNList, Option.some.injEq] at ha
    subst ha; simpa using hb
  | cons x xs ih =>
    intro ys a b ha hb
    simp only [Frontend.denoteNList] at ha
    cases hx : denoteN st x with
    | none => rw [hx] at ha; simp at ha
    | some y =>
      cases hxs : Frontend.denoteNList st xs with
      | none => rw [hx, hxs] at ha; simp at ha
      | some zs =>
        rw [hx, hxs] at ha
        obtain rfl := (Option.some.inj ha).symm
        simp only [List.cons_append, Frontend.denoteNList, hx, ih hxs hb]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1278-1283 nestBlockOf
The recorded block, exactly con-leche's. -/
theorem nestBlockOf_rel {env : Env} {fe : IFEnv} {s : AState} (hok : StateOK s)
    (hie : IFEnvOK env fe s) (ctxP : ConLeche.NestCtx) (hfind : ctxP.find? = env.find?)
    {C : NIdx} {CP : ConLeche.Name} (hC : denoteN s.store.ns C = some CP) :
    Frontend.denoteNList s.store.ns (Arena.nestBlockOf fe C) =
      some (ConLeche.nestBlockOf ctxP CP) := by
  simp only [Arena.nestBlockOf, ConLeche.nestBlockOf, hfind]
  cases hf : fe.find? C with
  | none => rw [hie.miss hok hC hf]; rfl
  | some ci =>
    obtain ⟨c, hc, he⟩ := find_some_rel hie hC hf
    rw [he]
    cases ci with
    | indInfo cv caps =>
      obtain ⟨cvP, capsP, -, hcaps, rfl⟩ := denoteCI_indInfo_inv hc
      exact (denoteCaps_inv hcaps).1
    | _ =>
      have := denoteCI_not_ind hc (by intro v caps h; exact nomatch h)
      cases c with
      | indInfo v k => exact absurd rfl (this v k)
      | _ => rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1285-1291 nestFrameMates
— the twin's one-pass loop, on names. -/
def matesGo (C : ConLeche.Name) : List ConLeche.Name → List ConLeche.Name → List ConLeche.Name
  | [], out => out
  | n :: ns, out =>
    if n == C || out.contains n then matesGo C ns out else matesGo C ns (out ++ [n])

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1285-1291 nestFrameMates
— **the one pass IS `eraseDups` then `filter`**: the loop's output is the
dedup accumulator, `C` filtered out. -/
theorem matesGo_eq (C : ConLeche.Name) :
    ∀ (l acc out : List ConLeche.Name), out = acc.reverse.filter (· != C) →
      matesGo C l out = (List.eraseDupsBy.loop (fun a b => a == b) l acc).filter (· != C) := by
  intro l
  induction l with
  | nil =>
    intro acc out h
    simp only [matesGo, List.eraseDupsBy.loop]
    exact h
  | cons a l ih =>
    intro acc out h
    simp only [matesGo, List.eraseDupsBy.loop]
    by_cases ha : a = C
    · subst ha
      simp only [beq_self_eq_true, Bool.true_or, if_true]
      split
      · exact ih acc out h
      · refine ih (a :: acc) out ?_
        simp [h]
    · have hne : (a == C) = false := by simpa using ha
      simp only [hne, Bool.false_or]
      by_cases hin : out.contains a = true
      · rw [if_pos hin]
        have hacc : acc.any (fun b => a == b) = true := by
          rw [h] at hin
          simp only [List.contains_iff_mem, List.mem_filter, List.mem_reverse] at hin
          simp only [List.any_eq_true, beq_iff_eq]
          exact ⟨a, hin.1, rfl⟩
        simp only [hacc]
        exact ih acc out h
      · rw [if_neg hin]
        have hacc : ¬ acc.any (fun b => a == b) = true := by
          intro hc
          apply hin
          rw [h]
          simp only [List.any_eq_true, beq_iff_eq] at hc
          obtain ⟨b, hb, rfl⟩ := hc
          simp only [List.contains_iff_mem, List.mem_filter, List.mem_reverse, bne_iff_ne,
            ne_eq]
          exact ⟨hb, ha⟩
        simp only [Bool.not_eq_true] at hacc
        simp only [hacc]
        refine ih (a :: acc) (out ++ [a]) ?_
        simp [h, ha]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1285-1291 nestFrameMates
— the twin's loop over handles denotes `matesGo`. -/
theorem nestFrameMatesGo_rel {st : EStore} (hwf : StoreWF st) {C : NIdx}
    {CP : ConLeche.Name} (hC : denoteN st.ns C = some CP) :
    ∀ (l out : List NIdx) (lP outP : List ConLeche.Name),
      Frontend.denoteNList st.ns l = some lP → Frontend.denoteNList st.ns out = some outP →
      Frontend.denoteNList st.ns (Arena.nestFrameMates.go C l out) = some (matesGo CP lP outP) := by
  intro l
  induction l with
  | nil =>
    intro out lP outP hl ho
    simp only [Frontend.denoteNList, Option.some.injEq] at hl
    subst hl
    simpa [Arena.nestFrameMates.go, matesGo] using ho
  | cons a l ih =>
    intro out lP outP hl ho
    simp only [Frontend.denoteNList] at hl
    cases ha : denoteN st.ns a with
    | none => rw [ha] at hl; simp at hl
    | some aP =>
    cases hls : Frontend.denoteNList st.ns l with
    | none => rw [ha, hls] at hl; simp at hl
    | some lsP =>
    rw [ha, hls] at hl
    obtain rfl := (Option.some.inj hl).symm
    simp only [Arena.nestFrameMates.go, matesGo, beq_handle_eq hwf ha hC,
      contains_handle_eq hwf ha ho]
    split
    · exact ih out lsP outP hls ho
    · exact ih (out ++ [a]) lsP (outP ++ [aP]) hls
        (denoteNList_append ho (by simp [Frontend.denoteNList, ha]))

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1285-1291 nestFrameMates
A frame's group-mates, exactly con-leche's. -/
theorem nestFrameMates_rel {env : Env} {fe : IFEnv} {s : AState} (hok : StateOK s)
    (hie : IFEnvOK env fe s) (ctxP : ConLeche.NestCtx) (hfind : ctxP.find? = env.find?)
    {C : NIdx} {CP : ConLeche.Name} (hC : denoteN s.store.ns C = some CP) :
    Frontend.denoteNList s.store.ns (Arena.nestFrameMates fe C) =
      some (ConLeche.nestFrameMates ctxP CP) := by
  simp only [Arena.nestFrameMates, ConLeche.nestFrameMates]
  rw [nestFrameMatesGo_rel hok.wf hC _ _ _ [] (nestBlockOf_rel hok hie ctxP hfind hC) rfl,
    matesGo_eq CP _ [] [] rfl]
  rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1293-1307 nestArity
A frame hole's full arity, exactly con-leche's. -/
theorem nestArity_spec {env : Env} {fe : IFEnv} (ctxP : ConLeche.NestCtx)
    (hfind : ctxP.find? = env.find?) (C : NIdx) (CP : ConLeche.Name) :
    PSpec (fun st => IFEnvOKS env fe st ∧ denoteN st.ns C = some CP)
      (Arena.nestArity fe C) (RV (ConLeche.nestArity ctxP CP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hie, hC⟩ := hp
  have hie' := hie s₀ rfl
  simp only [Arena.nestArity] at hrun
  simp only [RV, ConLeche.nestArity, hfind]
  cases hf : fe.find? C with
  | none =>
    rw [hf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    rw [hie'.miss hok hC hf]
    exact ⟨PStep.refl hok, rfl⟩
  | some ci =>
    rw [hf] at hrun
    obtain ⟨c, hc, he⟩ := find_some_rel hie' hC hf
    rw [he]
    cases ci with
    | indInfo cv caps =>
      obtain ⟨cvP, capsP, hcv, -, rfl⟩ := denoteCI_indInfo_inv hc
      obtain ⟨-, -, hty⟩ := denoteCV_inv hcv
      dsimp only at hrun
      obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨p1, hq1, -⟩ := piBinders_spec _ _ _ s₀ s₁ q hok hty h1
      obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨p1, denoteBinders_length hq1⟩
    | _ =>
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      have := denoteCI_not_ind hc (by intro v caps h; exact nomatch h)
      refine ⟨PStep.refl hok, ?_⟩
      cases c with
      | indInfo v k => exact absurd rfl (this v k)
      | _ => rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1264-1276 nestGroupCtors
The constructors of every container in `cs`, the accumulator the prefix of
con-leche's answer; con-leche's run succeeds with the rest. -/
theorem nestGroupCtors_spec {env : Env} {fe : IFEnv} (ctxP : ConLeche.NestCtx)
    (hfind : ctxP.find? = env.find?) (nPc : Nat) :
    ∀ (cs : List NIdx) (csP : List ConLeche.Name) (out : List (IConstantVal × Nat))
      (outP : List (ConstantVal × Nat)),
    PSpec (fun st => IFEnvOKS env fe st ∧ Frontend.denoteNList st.ns cs = some csP ∧
        dCtors st out = some outP)
      (Arena.nestGroupCtors fe nPc cs out)
      (fun st r => ∃ v, dCtors st r = some (outP ++ v) ∧
        FOk (ConLeche.nestGroupCtors (m := FueledM) ctxP nPc csP) v) := by
  intro cs
  induction cs with
  | nil =>
    intro csP out outP s₀ s' r hok hp hrun
    obtain ⟨-, hcs, hout⟩ := hp
    simp only [Frontend.denoteNList, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.nestGroupCtors] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], by simpa using hout, FOk.pure _⟩
  | cons c cs ih =>
    intro csP out outP s₀ s' r hok hp hrun
    obtain ⟨hie, hcs, hout⟩ := hp
    simp only [Frontend.denoteNList] at hcs
    cases hc : denoteN s₀.store.ns c with
    | none => rw [hc] at hcs; simp at hcs
    | some cP =>
    cases hcs' : Frontend.denoteNList s₀.store.ns cs with
    | none => rw [hc, hcs'] at hcs; simp at hcs
    | some csP' =>
    rw [hc, hcs'] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    simp only [Arena.nestGroupCtors] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := nestContainer_spec ctxP hfind c cP s₀ s₁ o hok ⟨hie, hc⟩ h1
    cases o with
    | none => exact absurd h2 (fun hc => failOk hc)
    | some q =>
      obtain ⟨nPc2, ctors⟩ := q
      obtain ⟨qP, hqP, hq1, hq2⟩ := ho
      dsimp only at h2 hq1 hq2
      have hlen := mapM_option_length hq2
      by_cases hg : (!(nPc2 == nPc || ctors.length == 0)) = true
      · rw [if_pos hg] at h2; exact absurd h2 (fun hc => failOk hc)
      · rw [if_neg hg] at h2
        have hout1 : dCtors s₁.store out = some outP := dCtors_ext p1.ext _ _ hout
        obtain ⟨p2, v, hv, hF⟩ := ih csP' (out ++ ctors) (outP ++ qP.2) s₁ s' r p1.ok
          ⟨hie.mono p1.ext, denoteNListE_ext p1.ext _ _ hcs', mapM_option_append hout1 hq2⟩ h2
        refine ⟨p1.trans p2, qP.2 ++ v, by simpa using hv, ?_⟩
        have hg' : (qP.1 == nPc || qP.2.isEmpty) = true := by
          simp only [Bool.not_eq_true'] at hg
          rw [← hq1]
          cases h : (nPc2 == nPc) with
          | true => rfl
          | false =>
            rw [h, Bool.false_or] at hg
            simp only [Bool.false_or]
            rw [List.isEmpty_iff_length_eq_zero, hlen]
            simpa using hg
        simp only [ConLeche.nestGroupCtors, hqP]
        refine FOk.bind FOk.unwrapOr ?_
        exact FOk.ite_pos hg' (FOk.bind hF (FOk.pure _))

/-! ## The instantiation's former: `nestInstType`, `nestGrowGroup` -/

/-- con-leche: none — `viewLsLen`, as a run. -/
theorem viewLsLen_run {s s' : AState} {h : LsIdx} {r : Option Nat}
    (hrun : viewLsLen h s = .ok (r, s')) : s' = s ∧ r = s.store.lss.viewLen h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewLsLen_spec s h)

section InstType

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1118-1158 nestInstType
The instantiation's type former, checked as con-leche checks it: the index
count and the container's type at the key, and (con-leche's
`nestInstTypeS_sim`) that type is well scoped wherever the key's parameters
are. -/
theorem nestInstType_spec {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP)
    (ctx : Arena.NestCtx) (hi : Nat) (key : Arena.NestKey) (keyP : ConLeche.NestKey) :
    CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧ dKey st key = some keyP)
      (Arena.nestInstType fe ctx hi key)
      (fun st r v => r.1 = v.1 ∧ denoteE st r.2 = some v.2 ∧
        ∀ d, (∀ x ∈ keyP.ds, Expr.WScoped d x) → Expr.WScoped d v.2)
      (ConLeche.nestInstType (m := FueledM) ctxP hi keyP) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hctx, hkey⟩ := hp
  obtain ⟨hcn, hlv, hds⟩ := dKey_inv hkey
  obtain ⟨namesP, lpsP, paramsP, sortP, rfl, hnames, hlps, hparams, hsort, hlvls⟩ :=
    dCtx_inv hctx
  simp only [Arena.nestInstType] at hrun
  obtain ⟨cv, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hcv, hs1⟩ := unwrapOr_ok h1
  rw [hs1] at h2
  cases hf : fe.find? key.cname with
  | none => rw [hf] at hcv; exact nomatch hcv
  | some ci =>
  rw [hf] at hcv
  obtain ⟨cv0, caps0, rfl, rfl⟩ : ∃ cv0 caps0, ci = .indInfo cv0 caps0 ∧ cv0 = cv := by
    cases ci <;> simp_all
  obtain ⟨c, hci, he⟩ := find_some_rel hok.ienv hcn hf
  obtain ⟨cvP, capsP, hcvP, -, rfl⟩ := denoteCI_indInfo_inv hci
  obtain ⟨-, hlpsC, htyC⟩ := denoteCV_inv hcvP
  have hcl : cvP.type.hasFvar = false := hc _ _ he
  obtain ⟨nl, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨hs2, hnl⟩ := viewLsLen_run h3
  rw [hs2] at h4
  rw [Core.viewLen_of_denoteLs hlv] at hnl
  subst hnl
  dsimp only at h4
  have hlenC := PW.denoteNList_length hlpsC
  by_cases hlen : (keyP.lvls.length != cv0.levelParams.length) = true
  · rw [if_pos hlen] at h4; exact absurd h4 (fun hc => failOk hc)
  rw [if_neg hlen] at h4
  have hlen' : keyP.lvls.length = cvP.levelParams.length := by
    rw [← hlenC]; simpa using hlen
  obtain ⟨o, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨hs3, hbp⟩ := stripPis_pstep hok.state htyC h5
  rw [hs3] at h6
  cases o with
  | none => exact absurd h6 (fun hc => failOk hc)
  | some q =>
  obtain ⟨xs, x, hsp, -⟩ := stripPis_some hbp
  rw [PW.denoteEList_length hds] at hsp
  dsimp only at h6
  obtain ⟨tl, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨c4, htl⟩ := instLPFast_cstep hok hlpsC hlv htyC h7
  obtain ⟨o2, s₅, h9, h10⟩ := bindOk h8
  obtain ⟨p5, ho2⟩ := instPisWith_spec key.ds keyP.ds tl _ s₄ s₅ o2 c4.ok.state
    ⟨denoteEList_ext c4.ext _ _ hds, htl⟩ h9
  have c5 := c4.trans (p5.toCore c4.ok)
  cases o2 with
  | none => exact absurd h10 (fun hc => failOk hc)
  | some ty =>
  obtain ⟨tyP, hinst, hty⟩ := ho2
  dsimp only at h10
  obtain ⟨pb, s₆, h11, h12⟩ := bindOk h10
  obtain ⟨p6, hpb1, hpb2⟩ := piBinders_spec _ ty tyP s₅ s₆ pb c5.ok.state hty h11
  have c6 := c5.trans (p6.toCore c5.ok)
  obtain ⟨bs, res⟩ := pb
  dsimp only at h12 hpb1 hpb2
  obtain ⟨v, s₇, h13, h14⟩ := bindOk h12
  obtain ⟨hs7, hv⟩ := view_run h13
  rw [hs7] at h14
  cases v
  case sort sL =>
    obtain ⟨sP, hres, hsL⟩ := denote_sort_inv c6.ok.state.wf hv hpb2
    dsimp only at h14
    obtain ⟨b, s₈, h15, h16⟩ := bindOk h14
    have hnames6 := denoteNListE_ext (c4.ext.trans (p5.ext.trans p6.ext)) _ _ hnames
    obtain ⟨p8, hb⟩ := anyM_B_pstep (fun st => Frontend.denoteNList st.ns ctx.names = some namesP)
      (fun hx h => denoteNListE_ext hx _ _ h)
      (fun b bP s₀ s' x hok' hq hd _ hrun' =>
        nestOcc_spec ctx.names namesP ctx.nP hi b.1 bP.1 s₀ s' x hok' ⟨hq, hd⟩ hrun')
      bs _ s₆ s₈ b c6.ok.state hnames6 hpb1 h15
    have c8 := c6.trans (p8.toCore c6.ok)
    cases b with
    | true => exact absurd h16 (fun hc => failOk hc)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h16
    obtain ⟨o3, s₉, h17, h18⟩ := bindOk h16
    have hsort8 := denoteL_ext hsort (c4.ext.trans (p5.ext.trans (p6.ext.trans p8.ext)))
    have hsL8 := denoteL_ext hsL p8.ext
    obtain ⟨c9o, c9s, c9p, lu, lv, hlu, hlvv, ho3⟩ :=
      AM.of_run (P := fun t => t = s₈) rfl h17 (Core.lvlEq?_spec s₈ sL ctx.sort c8.ok)
    rw [hsL8] at hlu; obtain rfl := Option.some.inj hlu
    rw [hsort8] at hlvv; obtain rfl := Option.some.inj hlvv
    have c9 : CoreStep μ env fe s₈ s₉ := ⟨c9o, by rw [c9s]; exact Ext.refl _, c9p⟩
    obtain ⟨ok, s₁₀, h19, h20⟩ := bindOk h18
    obtain ⟨ho3', hs10⟩ := liftFueled_ok h19
    rw [hs10] at h20
    cases ok with
    | false => exact absurd h20 (fun hc => failOk hc)
    | true =>
    simp only [↓reduceIte] at h20
    obtain ⟨rfl, rfl⟩ := pureOk h20
    have hall := c8.trans c9
    refine ⟨hall, (tyP.piBinders.1.length, tyP),
      ⟨denoteBinders_length hpb1, denote_ext hty (p6.ext.trans (p8.ext.trans c9.ext)),
        fun d hd => wscoped_instPisWith hd (Expr.WScoped.of_not_hasFvar
          (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcl)) hinst⟩, ?_⟩
    simp only [ConLeche.nestInstType, he]
    refine FOk.bind FOk.unwrapOr ?_
    rw [if_pos hlen', if_pos (by rw [hsp]; rfl), hinst]
    refine FOk.bind FOk.unwrapOr ?_
    simp only [hres]
    refine FOk.bind FOk.unwrapOr ?_
    rw [if_neg (by rw [← hb]; decide), ← ho3, ho3']
    exact FOk.bind FOk.liftFueled (FOk.pure _)
  all_goals exact absurd h14 (fun hc => failOk hc)

end InstType

/-! ### The group records -/

/-- con-leche: none — a group entry `(C, type of its hole)`, denoted. -/
def dGE (st : EStore) (p : NIdx × EIdx) : Option (ConLeche.Name × Expr) :=
  (denoteN st.ns p.1).bind fun c => (denoteE st p.2).map (c, ·)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1309-1316 nestGrowGroup
(`grp`) — a frame's group, denoted. -/
def dGrp (st : EStore) (g : List (NIdx × EIdx)) : Option (List (ConLeche.Name × Expr)) :=
  g.mapM (dGE st)

theorem dGE_ext : DExt dGE := by
  intro st st' hx p y h
  simp only [dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
  obtain ⟨c, hc, t, ht, rfl⟩ := h
  exact ⟨c, denoteN_ext hc hx, t, denote_ext ht hx, rfl⟩

theorem dGrp_ext : DExt dGrp := dGE_ext.list

theorem dGrp_names {st : EStore} :
    ∀ {g : List (NIdx × EIdx)} {gP : List (ConLeche.Name × Expr)}, dGrp st g = some gP →
      Frontend.denoteNList st.ns (g.map Prod.fst) = some (gP.map Prod.fst) := by
  intro g
  induction g with
  | nil => intro gP h; simp only [dGrp, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
           subst h; rfl
  | cons p g ih =>
    intro gP h
    simp only [dGrp, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hp : dGE st p with
    | none => rw [hp] at h; simp at h
    | some y =>
      cases hg : g.mapM (dGE st) with
      | none => rw [hp, hg] at h; simp at h
      | some ys =>
        rw [hp, hg] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
        obtain ⟨c, hc, t, ht, rfl⟩ := hp
        simp only [List.map_cons, Frontend.denoteNList, hc, ih hg]

section Grow

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1309-1316 nestGrowGroup
A frame's group grown by the named containers, exactly con-leche's (the
accumulator is con-leche's own), each hole's type well scoped wherever the
frame's parameters are (con-leche's `nestGrowGroupS_sim`). -/
theorem nestGrowGroup_spec {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP)
    (ctx : Arena.NestCtx) (hi : Nat) (us : LsIdx) (usP : List Level) (ds : List EIdx)
    (dsP : List Expr) :
    ∀ (cs : List NIdx) (csP : List ConLeche.Name) (grp : List (NIdx × EIdx))
      (grpP : List (ConLeche.Name × Expr)),
      (∀ x ∈ grpP, ∀ d, (∀ y ∈ dsP, Expr.WScoped d y) → Expr.WScoped d x.2) →
      CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
          denoteLs st.lss us = some usP ∧ Frontend.denoteEList st ds = some dsP ∧
          Frontend.denoteNList st.ns cs = some csP ∧ dGrp st grp = some grpP)
        (Arena.nestGrowGroup fe ctx hi us ds cs grp)
        (fun st r v => dGrp st r = some v ∧
          ∀ x ∈ v, ∀ d, (∀ y ∈ dsP, Expr.WScoped d y) → Expr.WScoped d x.2)
        (ConLeche.nestGrowGroup (m := FueledM) ctxP hi usP dsP csP grpP) := by
  intro cs
  induction cs with
  | nil =>
    intro csP grp grpP hg s₀ s' r hok hp hrun
    obtain ⟨-, -, -, hcs, hgrp⟩ := hp
    simp only [Frontend.denoteNList, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.nestGrowGroup] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, grpP, ⟨hgrp, hg⟩, FOk.pure _⟩
  | cons c cs ih =>
    intro csP grp grpP hg s₀ s' r hok hp hrun
    obtain ⟨hctx, hus, hds, hcs, hgrp⟩ := hp
    simp only [Frontend.denoteNList] at hcs
    cases hcn : denoteN s₀.store.ns c with
    | none => rw [hcn] at hcs; simp at hcs
    | some cP =>
    cases hcs' : Frontend.denoteNList s₀.store.ns cs with
    | none => rw [hcn, hcs'] at hcs; simp at hcs
    | some csP' =>
    rw [hcn, hcs'] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    simp only [Arena.nestGrowGroup] at hrun
    obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨c1, v1, ⟨hv1a, hv1b, hv1c⟩, hF1⟩ := nestInstType_spec hc ctx hi ⟨c, us, ds⟩
      ⟨cP, usP, dsP⟩ s₀ s₁ q hok ⟨hctx, by simp [dKey, hcn, hus, hds]⟩ h1
    obtain ⟨n1, cty⟩ := q
    dsimp only at h2 hv1a hv1b
    have hgrp1 : dGrp s₁.store (grp ++ [(c, cty)]) = some (grpP ++ [(cP, v1.2)]) :=
      mapM_option_append (dGrp_ext c1.ext _ _ hgrp)
        (by simp [dGE, denoteN_ext hcn c1.ext, hv1b])
    obtain ⟨c2, v, ⟨hv, hvs⟩, hF⟩ := ih csP' (grp ++ [(c, cty)]) (grpP ++ [(cP, v1.2)])
      (fun x hx d hd => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hg x hx d hd
        · simp only [List.mem_singleton] at hx; subst hx; exact hv1c d hd)
      s₁ s' r c1.ok
      ⟨dCtx_ext _ c1.ext _ _ hctx, denoteLs_ext hus c1.ext, denoteEList_ext c1.ext _ _ hds,
        denoteNListE_ext c1.ext _ _ hcs', hgrp1⟩ h2
    refine ⟨c1.trans c2, v, ⟨hv, hvs⟩, ?_⟩
    simp only [ConLeche.nestGrowGroup]
    exact FOk.bind hF1 hF

end Grow

/-! ## The canonical crests: `nestCanonCrest`, `nestCrest` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1097-1102 nestCanonCrest
A stored constructor type, canonically abstracted: exactly con-leche's,
`none` included. -/
theorem nestCanonCrest_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (us : LsIdx) (usP : List Level) (n : Nat) (cty : EIdx) (ctyP : Expr) :
    PSpecP (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss us = some usP ∧ denoteE st cty = some ctyP)
      (Arena.nestCanonCrest names us n cty)
      (ROp RE (ConLeche.nestCanonCrest namesP usP n ctyP)) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hN, hU, hC⟩ := hp
  simp only [Arena.nestCanonCrest] at hrun
  obtain ⟨phs, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hphs⟩ := nestPhs_spec n s₀ s₁ phs hok hpins trivial h1
  obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨p2, ho⟩ := instPisWith_spec phs _ cty ctyP s₁ s₂ o p1.ok
    ⟨hphs, denote_ext hC p1.ext⟩ h3
  simp only [ConLeche.nestCanonCrest]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨p1.trans p2, ?_⟩
    simp only [ROp] at ho ⊢
    rw [ho]; rfl
  | some t =>
    obtain ⟨tP, htP, ht⟩ := ho
    dsimp only at h4
    obtain ⟨r1, s₃, h5, h6⟩ := bindOk h4
    have p12 := p1.trans p2
    obtain ⟨p3, hr1⟩ := replaceApps_spec names namesP us usP 0 n t tP s₂ s₃ r1 p12.ok
      (Inductives.PinsOK.ofPStep hpins p12) ⟨denoteNListE_ext p12.ext _ _ hN, denoteLs_ext hU p12.ext, ht⟩ h5
    obtain ⟨rfl, rfl⟩ := pureOk h6
    exact ⟨p12.trans p3, _, by rw [htP]; rfl, hr1⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1110-1116 nestCrest
A stored constructor type at a key, exactly con-leche's, `none` included. -/
theorem nestCrest_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (us : LsIdx) (usP : List Level) (ds : List EIdx) (dsP : List Expr) (holes : List EIdx)
    (holesP : List Expr) (cty : EIdx) (ctyP : Expr) :
    PSpecP (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss us = some usP ∧ Frontend.denoteEList st ds = some dsP ∧
        Frontend.denoteEList st holes = some holesP ∧ denoteE st cty = some ctyP)
      (Arena.nestCrest names us ds holes cty)
      (ROp RE (ConLeche.nestCrest namesP usP dsP holesP ctyP)) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hN, hU, hD, hH, hC⟩ := hp
  simp only [Arena.nestCrest] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := nestCanonCrest_spec names namesP us usP ds.length cty ctyP s₀ s₁ o hok
    hpins ⟨hN, hU, hC⟩ h1
  rw [PW.denoteEList_length hD] at ho
  simp only [ConLeche.nestCrest]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨p1, ?_⟩
    simp only [ROp] at ho ⊢
    rw [ho]; rfl
  | some c =>
    obtain ⟨cP, hcP, hc⟩ := ho
    dsimp only at h2
    obtain ⟨r1, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨p2, hr1⟩ := replaceFVars_spec (.keyMap ds holes) (ConLeche.nestKeyMap dsP holesP) c
      cP s₁ s₂ r1 p1.ok (Inductives.PinsOK.ofPStep hpins p1)
      ⟨⟨dsP, holesP, denoteEList_ext p1.ext _ _ hD, denoteEList_ext p1.ext _ _ hH, rfl⟩, hc⟩ h3
    obtain ⟨rfl, rfl⟩ := pureOk h4
    exact ⟨p1.trans p2, _, by rw [hcP]; rfl, hr1⟩

/-! ## The constructor's result and record: `nestResHead`, `nestCtorNf` -/

/-- con-leche: none — a denoting handle's `fvar` tag test is its term's
shape test. -/
theorem tag_fvar_eq {st : EStore} (hwf : StoreWF st) {h : EIdx} {g : Expr}
    (hd : denoteE st h = some g) :
    (h.tag == ETag.fvar) = (match g with | .fvar .. => true | _ => false) := by
  obtain ⟨v, hv, ht, hdv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;>
    first
    | (obtain ⟨_, _, rfl⟩ := hdv; rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := hdv; rfl)
    | (obtain ⟨_, _, _, _, _, _, rfl⟩ := hdv; rfl)
    | (subst hdv; rfl)
    | rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1160-1167 nestResHead
A constructor's result is headed by a variable, exactly con-leche's test. -/
theorem nestResHead_spec (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP) (Arena.nestResHead e)
      (RV (ConLeche.nestResHead eP)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.nestResHead] at hrun
  obtain ⟨hd', s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hs1, hhd⟩ := getAppFn_run hok hd h1
  rw [hs1] at h2
  obtain ⟨rfl, rfl⟩ := pureOk h2
  refine ⟨PStep.refl hok, ?_⟩
  simp only [RV, ConLeche.nestResHead]
  generalize eP.getAppFn = g at hhd ⊢
  rw [tag_fvar_eq hok.wf hhd]
  cases g <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1188-1196 nestCtorNf
A frame constructor's record, read back: con-leche's at the walked telescope
the caller closed (`closeTelescope nds hi cur`, computed once by the twin). -/
theorem nestCtorNf_spec (ctx : Arena.NestCtx) (prog : List Arena.NestHole) (us : LsIdx)
    (ds : List EIdx) (cv : IConstantVal) (closed : EIdx)
    (fnd : ConLeche.Name → Option ConstantInfo) (ctxP : ConLeche.NestCtx)
    (progP : List ConLeche.NestHole) (usP : List Level) (dsP : List Expr) (cvP : ConstantVal)
    (closedP : Expr) :
    PSpecP (fun st => dCtx st fnd ctx = some ctxP ∧ dProg st prog = some progP ∧
        denoteLs st.lss us = some usP ∧ Frontend.denoteEList st ds = some dsP ∧
        Frontend.denoteCV st cv = some cvP ∧ denoteE st closed = some closedP)
      (Arena.nestCtorNf ctx prog us ds cv closed)
      (fun st r => dCtorNf st r = some ⟨cvP.name, usP,
        dsP.map (·.replaceFVars (ConLeche.nestHoleImg ctxP progP)),
        closedP.replaceFVars (ConLeche.nestHoleImg ctxP progP)⟩) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hctx, hprog, hU, hD, hcv, hcl⟩ := hp
  obtain ⟨hname, -, -⟩ := denoteCV_inv hcv
  simp only [Arena.nestCtorNf] at hrun
  have hrel : ∀ st, dCtx st fnd ctx = some ctxP → dProg st prog = some progP →
      FvMapRel st (.holeImg ctx prog prog.length) (ConLeche.nestHoleImg ctxP progP) :=
    fun st h1 h2 => ⟨fnd, ctxP, progP, h1, by rw [List.take_length]; exact h2, Nat.le_refl _, rfl⟩
  obtain ⟨ds2, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hds2⟩ := mapM_RE_P (fun st => dCtx st fnd ctx = some ctxP ∧
      dProg st prog = some progP)
    (fun hx h => ⟨dCtx_ext fnd hx _ _ h.1, dProg_ext hx _ _ h.2⟩)
    (fun e eP s₀ s' r hok hpins hp hrun =>
      replaceFVars_spec _ _ e eP s₀ s' r hok hpins ⟨hrel _ hp.1.1 hp.1.2, hp.2⟩ hrun)
    ds dsP s₀ s₁ ds2 hok hpins ⟨⟨hctx, hprog⟩, hD⟩ h1
  obtain ⟨ty, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨p2, hty⟩ := replaceFVars_spec _ _ closed closedP s₁ s₂ ty p1.ok (Inductives.PinsOK.ofPStep hpins p1)
    ⟨hrel _ (dCtx_ext fnd p1.ext _ _ hctx) (dProg_ext p1.ext _ _ hprog),
      denote_ext hcl p1.ext⟩ h3
  obtain ⟨rfl, rfl⟩ := pureOk h4
  refine ⟨p1.trans p2, ?_⟩
  simp only [dCtorNf, denoteN_ext hname (p1.ext.trans p2.ext),
    denoteLs_ext hU (p1.ext.trans p2.ext), denoteEList_ext p2.ext _ _ hds2, hty]
  rfl

/-! ## The parameters' free-variable test and the walk stack -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1714 fvarB — `fvarB`'s run at this
tier's frame: con-leche's `Expr.fvarB`, nothing framed moved. -/
theorem fvarB_pstep {fuel : Nat} {s₀ s' : AState} {e : EIdx} {eP : Expr} {r : Nat}
    (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.fvarB fuel e s₀ = .ok (r, s')) : PStep s₀ s' ∧ r = eP.fvarB := by
  obtain ⟨h1, h2, h3, h4⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.fvarB_spec fuel s₀ e hok (by rw [hd]; rfl))
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.wf⟩ (by rw [h1]; exact Ext.refl _)
    (by rw [h1]; exact BMExt.refl _) h2 h3, ?_⟩
  rw [h4 eP hd, Expr.fvarB_eq]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1353-1357 nestWalkStack
(`ds.all (·.fvarB ≤ hiAt 0)`) — the parameters-mention-no-frame-hole test, the
twin's `allM` over `fvarB`. -/
theorem closedAll_spec (h : Nat) (ds : List EIdx) (dsP : List Expr) :
    PSpec (fun st => Frontend.denoteEList st ds = some dsP)
      (ds.allM fun x => do
        let b ← fvarB coreWalkFuel x
        pure (decide (b ≤ h)))
      (RV (dsP.all fun x => decide (x.fvarB ≤ h))) := by
  intro s₀ s' r hok hd hrun
  exact allM_E_pstep (fun _ => True) (fun _ _ => trivial)
    (fun e eP s₀ s' b hok _ hd hrun => by
      obtain ⟨b0, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨p1, rfl⟩ := fvarB_pstep hok hd h1
      obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨p1, rfl⟩)
    ds dsP s₀ s' r hok trivial hd hrun

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1353-1357 nestWalkStack
The frame stack an instantiation is walked under, exactly con-leche's test. -/
theorem nestWalkStack_spec (ctx : Arena.NestCtx) (prog : List Arena.NestHole)
    (ds : List EIdx) (dsP : List Expr) :
    PSpec (fun st => Frontend.denoteEList st ds = some dsP)
      (Arena.nestWalkStack ctx prog ds)
      (RV (if (dsP.all fun x => decide (x.fvarB ≤ ctx.hiAt 0)) then [] else prog)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.nestWalkStack] at hrun
  obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hb⟩ := closedAll_spec (ctx.hiAt 0) ds dsP s₀ s₁ b hok hd h1
  simp only [RV] at hb
  subst hb
  by_cases hc : (dsP.all fun x => decide (x.fvarB ≤ ctx.hiAt 0)) = true
  · rw [if_pos hc] at h2; obtain ⟨rfl, rfl⟩ := pureOk h2
    exact ⟨p1, by simp only [RV, if_pos hc]⟩
  · rw [if_neg hc] at h2; obtain ⟨rfl, rfl⟩ := pureOk h2
    exact ⟨p1, by simp only [RV, if_neg hc]⟩

end ConRon.Bridge.Inductives
