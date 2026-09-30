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

end ConRon.Bridge.Inductives
