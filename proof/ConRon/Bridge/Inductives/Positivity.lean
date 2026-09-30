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
    (hfind : ctxP.find? = env.find?) (hcok : NestCtxOk ctxP) (nPc : Nat) :
    ∀ (cs : List NIdx) (csP : List ConLeche.Name) (out : List (IConstantVal × Nat))
      (outP : List (ConstantVal × Nat)),
    PSpec (fun st => IFEnvOKS env fe st ∧ Frontend.denoteNList st.ns cs = some csP ∧
        dCtors st out = some outP)
      (Arena.nestGroupCtors fe nPc cs out)
      (fun st r => ∃ v, dCtors st r = some (outP ++ v) ∧
        FOk (ConLeche.nestGroupCtors (m := FueledM) ctxP nPc csP) v ∧
        ∀ x ∈ v, x.1.type.hasFvar = false) := by
  intro cs
  induction cs with
  | nil =>
    intro csP out outP s₀ s' r hok hp hrun
    obtain ⟨-, hcs, hout⟩ := hp
    simp only [Frontend.denoteNList, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.nestGroupCtors] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], by simpa using hout, FOk.pure _, fun _ h => nomatch h⟩
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
        obtain ⟨p2, v, hv, hF, hvc⟩ := ih csP' (out ++ ctors) (outP ++ qP.2) s₁ s' r p1.ok
          ⟨hie.mono p1.ext, denoteNListE_ext p1.ext _ _ hcs', mapM_option_append hout1 hq2⟩ h2
        refine ⟨p1.trans p2, qP.2 ++ v, by simpa using hv, ?_, fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact Cached.nestContainer_closed hcok hqP x hx
          · exact hvc x hx⟩
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

/-! ## Helpers of the walk -/

/-- con-leche: none — `List.anyM` of a pure-grade test over a denoting handle
list: the verdict is the pure `List.any`. -/
theorem anyM_E_pstep {f : EIdx → AM Bool} {F : Expr → Bool} (Q : EStore → Prop)
    (hQx : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (hf : ∀ (e : EIdx) (eP : Expr) (s₀ s' : AState) (b : Bool), StateOK s₀ →
      Q s₀.store → denoteE s₀.store e = some eP → f e s₀ = .ok (b, s') →
      PStep s₀ s' ∧ b = F eP) :
    ∀ (hs : List EIdx) (xs : List Expr) (s₀ s' : AState) (b : Bool),
      StateOK s₀ → Q s₀.store → Frontend.denoteEList s₀.store hs = some xs →
      hs.anyM f s₀ = .ok (b, s') → PStep s₀ s' ∧ b = xs.any F := by
  intro hs
  induction hs with
  | nil =>
    intro xs s₀ s' b hok _ h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.anyM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons e es ih =>
    intro xs s₀ s' b hok hq h hrun
    obtain ⟨eP, esP, he, hes, rfl⟩ := denoteEList_cons h
    simp only [List.anyM] at hrun
    obtain ⟨c, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hc⟩ := hf e eP s₀ s1 c hok hq he k1
    cases c with
    | true =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      simp only [List.any_cons, ← hc, Bool.true_or]
    | false =>
      obtain ⟨p2, hb⟩ := ih esP s1 s' b p1.ok (hQx p1.ext hq)
        (denoteEList_ext p1.ext _ _ hes) z1
      refine ⟨p1.trans p2, ?_⟩
      simp only [List.any_cons, ← hc, Bool.false_or, hb]

/-- con-leche: none — `List.anyM` of a pure-grade test over
representation-free keys (indices): the verdict is the pure `List.any`. -/
theorem anyM_pstep {α : Type} {f : α → AM Bool} {g : α → Bool}
    (P : α → EStore → Prop)
    (hPx : ∀ {a : α} {st st' : EStore}, Ext st st' → P a st → P a st')
    (hf : ∀ (a : α) (s₀ s' : AState) (b : Bool), StateOK s₀ → P a s₀.store →
      f a s₀ = .ok (b, s') → PStep s₀ s' ∧ b = g a) :
    ∀ (xs : List α) (s₀ s' : AState) (b : Bool), StateOK s₀ →
      (∀ a ∈ xs, P a s₀.store) → xs.anyM f s₀ = .ok (b, s') →
      PStep s₀ s' ∧ b = xs.any g := by
  intro xs
  induction xs with
  | nil =>
    intro s₀ s' b hok _ hrun
    simp only [List.anyM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons a as ih =>
    intro s₀ s' b hok hP hrun
    simp only [List.anyM] at hrun
    obtain ⟨c, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hc⟩ := hf a s₀ s1 c hok (hP a (by simp)) k1
    cases c with
    | true =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      simp only [List.any_cons, ← hc, Bool.true_or]
    | false =>
      obtain ⟨p2, hb⟩ := ih s1 s' b p1.ok (fun x hx => hPx p1.ext (hP x (by simp [hx]))) z1
      refine ⟨p1.trans p2, ?_⟩
      simp only [List.any_cons, ← hc, Bool.false_or, hb]

/-- con-leche: none — `denoteEList` of a prefix. -/
theorem denoteEList_take' {st : EStore} :
    ∀ {xs : List EIdx} {xsP : List Expr} (n : Nat), Frontend.denoteEList st xs = some xsP →
      Frontend.denoteEList st (xs.take n) = some (xsP.take n) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP n h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h; simp [Frontend.denoteEList]
  | cons x xs ih =>
    intro xsP n h
    obtain ⟨y, ys, hy, hys, rfl⟩ := denoteEList_cons h
    cases n with
    | zero => simp [Frontend.denoteEList]
    | succ n => simp only [List.take_succ_cons, Frontend.denoteEList, hy, ih n hys]

/-- con-leche: none — `denoteEList` of a suffix. -/
theorem denoteEList_drop' {st : EStore} :
    ∀ {xs : List EIdx} {xsP : List Expr} (n : Nat), Frontend.denoteEList st xs = some xsP →
      Frontend.denoteEList st (xs.drop n) = some (xsP.drop n) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP n h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h; simp [Frontend.denoteEList]
  | cons x xs ih =>
    intro xsP n h
    obtain ⟨y, ys, hy, hys, rfl⟩ := denoteEList_cons h
    cases n with
    | zero => simpa using h
    | succ n => simp only [List.drop_succ_cons]; exact ih n hys

/-! ### The walk's state, denoted -/

theorem dState_inv {st : EStore} {ns : Arena.NestState} {nsP : ConLeche.NestState}
    (h : dState st ns = some nsP) :
    ns.keys.toList.mapM (dKey st) = some nsP.keys.toList ∧
      ns.active.mapM (dKey st) = some nsP.active ∧
      ns.ctorNfs.toList.mapM (dCtorNf st) = some nsP.ctorNfs.toList := by
  simp only [dState] at h
  cases h1 : ns.keys.toList.mapM (dKey st) with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : ns.active.mapM (dKey st) with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : ns.ctorNfs.toList.mapM (dCtorNf st) with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some c =>
  rw [h1, h2, h3] at h
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem dState_mk {st : EStore} {keys : Array Arena.NestKey} {active : List Arena.NestKey}
    {nfs : Array Arena.NestCtorNf} {keysP : Array ConLeche.NestKey}
    {activeP : List ConLeche.NestKey} {nfsP : Array ConLeche.NestCtorNf}
    (h1 : keys.toList.mapM (dKey st) = some keysP.toList)
    (h2 : active.mapM (dKey st) = some activeP)
    (h3 : nfs.toList.mapM (dCtorNf st) = some nfsP.toList) :
    dState st ⟨keys, active, nfs⟩ = some ⟨keysP, activeP, nfsP⟩ := by
  simp only [dState, h1, h2, h3, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Array.toArray_toList]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
(`st.ctorNfs.push`) — a record pushed onto the state. -/
theorem dState_push {st : EStore} {ns : Arena.NestState} {nsP : ConLeche.NestState}
    {nf : Arena.NestCtorNf} {nfP : ConLeche.NestCtorNf} (h : dState st ns = some nsP)
    (hn : dCtorNf st nf = some nfP) :
    dState st { ns with ctorNfs := ns.ctorNfs.push nf } =
      some { nsP with ctorNfs := nsP.ctorNfs.push nfP } := by
  obtain ⟨h1, h2, h3⟩ := dState_inv h
  exact dState_mk h1 h2 (by
    rw [Array.toList_push, Array.toList_push]
    exact mapM_option_append h3 (by simp [hn]))

/-- con-leche: none — a constructor's output `(kinds, walked form)`, denoted. -/
def dOut (st : EStore) (o : List Arena.NestFieldKind × EIdx) :
    Option (List ConLeche.NestFieldKind × Expr) :=
  (denoteE st o.2).map (o.1.map kindOf, ·)

theorem dOut_ext : DExt dOut := by
  intro st st' hx o y h
  simp only [dOut, Option.map_eq_some_iff] at h ⊢
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, denote_ext he hx, rfl⟩

/-- con-leche: none — the stack, appended at its inner end (the twin's), is
con-leche's with the new frames' holes reversed onto its front. -/
theorem dProg_append {st : EStore} {prog G : List Arena.NestHole}
    {progP GP : List ConLeche.NestHole} (hp : dProg st prog = some progP)
    (hG : G.mapM (dHole st) = some GP) : dProg st (prog ++ G) = some (GP.reverse ++ progP) := by
  simp only [dProg, Option.map_eq_some_iff] at hp ⊢
  obtain ⟨a, ha, rfl⟩ := hp
  exact ⟨a ++ GP, mapM_option_append ha hG, by simp⟩

theorem dProg_length {st : EStore} {prog : List Arena.NestHole}
    {progP : List ConLeche.NestHole} (hp : dProg st prog = some progP) :
    prog.length = progP.length := by
  simp only [dProg, Option.map_eq_some_iff] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  rw [List.length_reverse, mapM_option_length ha]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
(U4's kind test) — the twin's `(ks[i]?.map (· == .ordinary)).getD true` is
con-leche's `ks.getD i .ordinary == .ordinary` at the kinds read. -/
theorem u4_kind (ks : List Arena.NestFieldKind) (i : Nat) :
    ((ks[i]?.map (· == Arena.NestFieldKind.ordinary)).getD true) =
      !((ks.map kindOf).getD i .ordinary != .ordinary) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? with
  | none => rfl
  | some k => cases k <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
(`grp.mapIdx … Expr.fvar (hi + i) ty`) — the frame's holes, interned. -/
theorem frameHoles_run (hi : Nat) {f : (NIdx × EIdx) × Nat → AM EIdx}
    (hf : ∀ c ty i, f ((c, ty), i) = internFVarE (hi + i) ty) :
    ∀ (grp : List (NIdx × EIdx)) (grpP : List (ConLeche.Name × Expr)) (k : Nat)
      (s₀ s' : AState) (r : List EIdx), StateOK s₀ → dGrp s₀.store grp = some grpP →
      (grp.zipIdx k).mapM f s₀ = .ok (r, s') →
      PStep s₀ s' ∧ Frontend.denoteEList s'.store r =
        some ((grpP.zipIdx k).map fun p => Expr.fvar (hi + p.2) p.1.2) := by
  intro grp
  induction grp with
  | nil =>
    intro grpP k s₀ s' r hok hg hrun
    simp only [dGrp, List.mapM_nil, Option.pure_def, Option.some.injEq] at hg
    subst hg
    simp only [List.zipIdx_nil, List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons p grp ih =>
    intro grpP k s₀ s' r hok hg hrun
    simp only [dGrp, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hg
    cases hp : dGE s₀.store p with
    | none => rw [hp] at hg; simp at hg
    | some y =>
    cases hgs : grp.mapM (dGE s₀.store) with
    | none => rw [hp, hgs] at hg; simp at hg
    | some ys =>
    rw [hp, hgs] at hg
    simp only [Option.bind_some, Option.some.injEq] at hg
    subst hg
    obtain ⟨c, ty⟩ := p
    simp only [dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨cP, hcP, tyP, htyP, rfl⟩ := hp
    simp only [List.zipIdx_cons, List.mapM_cons, hf] at hrun
    obtain ⟨h1, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hh1⟩ := internFVarE_run hok htyP k1
    obtain ⟨hs, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hhs⟩ := ih ys (k + 1) s₁ s₂ hs p1.ok (dGrp_ext p1.ext _ _ hgs) k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, ?_⟩
    simp only [List.zipIdx_cons, List.map_cons, Frontend.denoteEList,
      denote_ext hh1 p2.ext, hhs]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1359-1382 nestContNew
(`grp.map (fun p => ⟨p.1, us, ds⟩)`) — the group's keys, denoted. -/
theorem dKeys_grp {st : EStore} {us : LsIdx} {usP : List Level} {ds : List EIdx}
    {dsP : List Expr} (hus : denoteLs st.lss us = some usP)
    (hds : Frontend.denoteEList st ds = some dsP) :
    ∀ {grp : List (NIdx × EIdx)} {grpP : List (ConLeche.Name × Expr)},
      dGrp st grp = some grpP →
      (grp.map fun (x : NIdx × EIdx) => (⟨x.1, us, ds⟩ : Arena.NestKey)).mapM (dKey st) =
        some (grpP.map fun p => (⟨p.1, usP, dsP⟩ : ConLeche.NestKey)) := by
  intro grp
  induction grp with
  | nil => intro grpP h; simp only [dGrp, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
           subst h; rfl
  | cons p grp ih =>
    intro grpP h
    simp only [dGrp, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hp : dGE st p with
    | none => rw [hp] at h; simp at h
    | some y =>
    cases hgs : grp.mapM (dGE st) with
    | none => rw [hp, hgs] at h; simp at h
    | some ys =>
    rw [hp, hgs] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    simp only [dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨cP, hcP, tyP, htyP, rfl⟩ := hp
    have := ih hgs
    simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def, this,
      Option.bind_some]
    simp [dKey, hcP, hus, hds]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
(the frame's stack entries) — the group's holes at `base`, denoted. -/
theorem dHoles_grp {st : EStore} {us : LsIdx} {usP : List Level} {ds : List EIdx}
    {dsP : List Expr} (hus : denoteLs st.lss us = some usP)
    (hds : Frontend.denoteEList st ds = some dsP) (b : Nat) :
    ∀ {grp : List (NIdx × EIdx)} {grpP : List (ConLeche.Name × Expr)},
      dGrp st grp = some grpP →
      (grp.map fun (x : NIdx × EIdx) => ({ key := ⟨x.1, us, ds⟩, base := b } : Arena.NestHole)).mapM
          (dHole st) =
        some (grpP.map fun p => ({ key := ⟨p.1, usP, dsP⟩, base := b } : ConLeche.NestHole)) := by
  intro grp
  induction grp with
  | nil => intro grpP h; simp only [dGrp, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
           subst h; rfl
  | cons p grp ih =>
    intro grpP h
    simp only [dGrp, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hp : dGE st p with
    | none => rw [hp] at h; simp at h
    | some y =>
    cases hgs : grp.mapM (dGE st) with
    | none => rw [hp, hgs] at h; simp at h
    | some ys =>
    rw [hp, hgs] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    simp only [dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hp
    obtain ⟨cP, hcP, tyP, htyP, rfl⟩ := hp
    have := ih hgs
    simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def, this,
      Option.bind_some]
    simp [dHole, dKey, hcP, hus, hds]

/-- con-leche: none — a binder telescope denotes, extended by one binder. -/
theorem denoteBinders_snoc {st : EStore} :
    ∀ {bs : List (EIdx × BinderMeta)} {bsP : List (Expr × BinderMeta)} {t : EIdx}
      {tP : Expr} (m : BinderMeta), denoteBinders st bs = some bsP →
      denoteE st t = some tP → denoteBinders st (bs ++ [(t, m)]) = some (bsP ++ [(tP, m)]) := by
  intro bs
  induction bs with
  | nil =>
    intro bsP t tP m h ht
    simp only [denoteBinders, Option.some.injEq] at h
    subst h
    simp [denoteBinders, ht]
  | cons b bs ih =>
    intro bsP t tP m h ht
    obtain ⟨x, mb⟩ := b
    simp only [denoteBinders] at h
    cases hx : denoteE st x with
    | none => rw [hx] at h; simp at h
    | some xP =>
    cases hbs : denoteBinders st bs with
    | none => rw [hx, hbs] at h; simp at h
    | some ys =>
    rw [hx, hbs] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.cons_append, denoteBinders, hx, ih m hbs ht]

/-! ## The positivity function and the container frames -/

section Walk

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Verify/Cached/NestPosC.lean RecSimC — `nestPos`'s
answer: the kind read, the walked form and the state denoting con-leche's, the
walked form well scoped at the walk's depth. -/
def RPos (dep : Nat) (st : EStore) (r : Arena.NestFieldKind × EIdx × Arena.NestState)
    (v : ConLeche.NestFieldKind × Expr × ConLeche.NestState) : Prop :=
  v.1 = kindOf r.1 ∧ denoteE st r.2.1 = some v.2.1 ∧ dState st r.2.2 = some v.2.2 ∧
    Expr.WScoped dep v.2.1

/-- con-leche: ConLeche/Verify/Cached/NestPosC.lean RecSimC — **`nestPos` at
`fuel` is correct**: at a well-scoped input, an accepting twin run denotes a
run of con-leche's `nestPos` at `fueledOpsM μ`. -/
def NestPosSpec (μ : CheckMode) (env : Env) (fe : IFEnv) (ctx : Arena.NestCtx)
    (ctxP : ConLeche.NestCtx) (fuel : Nat) : Prop :=
  ∀ (prog : List Arena.NestHole) (progP : List ConLeche.NestHole) (dep kb : Nat) (e : EIdx)
    (eP : Expr) (ns : Arena.NestState) (nsP : ConLeche.NestState), Expr.WScoped dep eP →
    CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
        dProg st prog = some progP ∧ denoteE st e = some eP ∧ dState st ns = some nsP)
      (Arena.nestPos μ fe ctx fuel prog dep kb e ns) (RPos dep)
      (ConLeche.nestPos (fueledOpsM μ) env ctxP fuel progP dep kb eP nsP)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1169-1186 nestFields
A constructor's field telescope through the walk at fuel `F` (con-leche's
`nestFieldsS_sim`): the accumulators are the prefix of con-leche's lists, every
walked domain well scoped at its own depth, the result at the depth past the
fields. -/
theorem nestFields_spec {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} {F : Nat}
    (hF : NestPosSpec μ env fe ctx ctxP F) (prog : List Arena.NestHole)
    (progP : List ConLeche.NestHole) (base : Nat) (err : ConLeche.CheckError) :
    ∀ (nF j : Nat) (cur : EIdx) (curP : Expr) (ns : Arena.NestState)
      (nsP : ConLeche.NestState) (ks : List Arena.NestFieldKind)
      (nds : List (EIdx × BinderMeta)) (ndsP : List (Expr × BinderMeta)),
      Expr.WScoped (base + j) curP →
      CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
          dProg st prog = some progP ∧ denoteE st cur = some curP ∧
          dState st ns = some nsP ∧ denoteBinders st nds = some ndsP)
        (Arena.nestFields μ fe ctx F prog base nF j cur ns ks nds)
        (fun st r v => r.1.map kindOf = ks.map kindOf ++ v.1 ∧
          denoteBinders st r.2.1 = some (ndsP ++ v.2.1) ∧ denoteE st r.2.2.1 = some v.2.2.1 ∧
          dState st r.2.2.2 = some v.2.2.2 ∧
          (∀ (i : Nat) (nd : Expr × BinderMeta), v.2.1[i]? = some nd →
            Expr.WScoped (base + j + i) nd.1) ∧
          Expr.WScoped (base + j + v.2.1.length) v.2.2.1)
        (ConLeche.nestFields (ConLeche.nestPos (fueledOpsM μ) env ctxP F) progP base err
          nF j curP nsP) := by
  intro nF
  induction nF with
  | zero =>
    intro j cur curP ns nsP ks nds ndsP hw s₀ s' r hok hp hrun
    obtain ⟨-, -, hcur, hns, hnds⟩ := hp
    rw [Arena.nestFields] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨CoreStep.refl hok, ([], [], curP, nsP), ⟨by simp, by simpa using hnds, hcur, hns,
      fun _ _ h => by simp at h, by simpa using hw⟩, ?_⟩
    simp only [ConLeche.nestFields]
    exact FOk.pure _
  | succ nF ih =>
    intro j cur curP ns nsP ks nds ndsP hw s₀ s' r hok hp hrun
    obtain ⟨hctx, hprog, hcur, hns, hnds⟩ := hp
    rw [Arena.nestFields] at hrun
    dsimp only at hrun
    by_cases htg : (cur.tag == ETag.forallE) = true
    · rw [if_pos htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨hs1, ho⟩ := viewBind_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some p =>
      obtain ⟨a, b, bm⟩ := p
      have hwv := view_of_viewBind_tag_forallE htg ho.symm
      obtain ⟨aP, bP, rfl, ha, hb⟩ := denote_forallE_inv hok.state.wf hwv hcur
      simp only [Expr.WScoped] at hw
      dsimp only at h2
      obtain ⟨q, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨c2, v1, ⟨hk1, hnd1, hns1, hwnd⟩, hF1⟩ :=
        hF prog progP (base + j) 0 a aP ns nsP hw.1 s₀ s₂ q hok ⟨hctx, hprog, ha, hns⟩ h3
      obtain ⟨k, nd, ns2⟩ := q
      dsimp only at h4 hk1 hnd1 hns1
      obtain ⟨fv, s₃, h5, h6⟩ := bindOk h4
      obtain ⟨p3, hfv⟩ := internFVarE_run c2.ok.state (denote_ext ha c2.ext) h5
      obtain ⟨b2, s₄, h7, h8⟩ := bindOk h6
      have hb3 : denoteE s₃.store b = some bP := denote_ext hb (c2.ext.trans p3.ext)
      obtain ⟨q1, q2, q3, q4, q5, -, q7⟩ := ExprOps.instantiate1Fast_run p3.ok hfv
        (by rw [hb3]; rfl) h7
      have p4 : PStep s₃ s₄ := PStep.of_caches q1 q2 q3 q4 q5
      have hb2 : denoteE s₄.store b2 = some (bP.instantiate1 (.fvar (base + j) aP) 0) :=
        q7 _ hb3
      have c4 := c2.trans ((p3.trans p4).toCore c2.ok)
      have hx34 := p3.ext.trans p4.ext
      have hw' : Expr.WScoped (base + (j + 1)) (bP.instantiate1 (.fvar (base + j) aP)) := by
        rw [show base + (j + 1) = base + j + 1 by omega]
        exact Expr.WScoped.instantiate1 hw.1 0 hw.2
      obtain ⟨c5, v2, ⟨hks2, hnds2, hres2, hns2, hwnds2, hwres2⟩, hF2⟩ :=
        ih (j + 1) b2 _ ns2 v1.2.2 (ks ++ [k]) (nds ++ [(nd, bm)]) (ndsP ++ [(v1.2.1, bm)]) hw'
          s₄ s' r c4.ok
          ⟨dCtx_ext _ (c2.ext.trans hx34) _ _ hctx, dProg_ext (c2.ext.trans hx34) _ _ hprog,
            hb2, dState_ext hx34 _ _ hns1,
            denoteBinders_snoc bm (denoteBinders_ext (c2.ext.trans hx34) _ _ hnds)
              (denote_ext hnd1 hx34)⟩ h8
      refine ⟨c4.trans c5, (v1.1 :: v2.1, (v1.2.1, bm) :: v2.2.1, v2.2.2.1, v2.2.2.2),
        ⟨?_, ?_, hres2, hns2, ?_, ?_⟩, ?_⟩
      · rw [hks2, hk1]; simp
      · rw [hnds2]; simp
      · intro i x hx
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx; simpa using hwnd
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          have := hwnds2 i x hx
          rwa [show base + (j + 1) + i = base + j + (i + 1) by omega] at this
      · simp only [List.length_cons]
        rw [show base + j + (v2.2.1.length + 1) = base + (j + 1) + v2.2.1.length by omega]
        exact hwres2
      · simp only [ConLeche.nestFields]
        exact FOk.bind hF1 (FOk.bind hF2 (FOk.pure _))
    · rw [if_neg htg] at hrun
      exact absurd hrun (fun hc => failOk hc)

end Walk

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:643-654 NestCtx — the
context's own fields, read off its denotation. -/
theorem dCtx_fields {st : EStore} {fnd : ConLeche.Name → Option ConstantInfo}
    {c : Arena.NestCtx} {cP : ConLeche.NestCtx} (h : dCtx st fnd c = some cP) :
    Frontend.denoteNList st.ns c.names = some cP.names ∧ c.nP = cP.nP ∧ cP.find? = fnd ∧
      Frontend.denoteEList st c.params = some cP.params ∧
      denoteLs st.lss c.lvls = some (cP.lps.map .param) ∧
      Frontend.denoteNList st.ns c.lps = some cP.lps := by
  obtain ⟨namesP, lpsP, paramsP, sortP, rfl, h1, h2, h3, h4, h5⟩ := dCtx_inv h
  exact ⟨h1, rfl, rfl, h3, h5, h2⟩

section Ctors

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: none — the twin's `if _h : root then (do let F ← m; k F) else k
fuel`, as ONE bind (the `do` elaborator duplicates the continuation into both
arms). -/
theorem dite_bind_AM {α β : Type} (b : Bool) (m : AM α) (a : α) (X : α → AM β) :
    (if _h : b = true then m >>= X else X a) = ((if b = true then m else pure a) >>= X) := by
  cases b <;> simp

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1198-1262 nestCtors
**A frame's constructors** (con-leche's `nestCtorsS_sim`), the root frame's
(`root`) and a container frame's alike: the twin's `root` flag and `fuel`
denote con-leche's continuation `rec` (`hrec`), and the walk is correct at the
fuel it runs at (`hps`).  The accumulator `outs` is the prefix of con-leche's
answer; every walked form is well scoped at the frame's depth. -/
theorem nestCtors_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (root : Bool) (fuel : Nat)
    (rec : Expr → List ConLeche.NestHole → Nat → Nat → Expr → ConLeche.NestState →
      FueledM (ConLeche.NestFieldKind × Expr × ConLeche.NestState))
    (hrec : ∀ crestP, rec crestP =
      ConLeche.nestPos (fueledOpsM μ) env ctxP (if root then whnfWalkFuel crestP else fuel))
    (hps : ∀ crestP, NestPosSpec μ env fe ctx ctxP (if root then whnfWalkFuel crestP else fuel))
    (prog : List Arena.NestHole) (progP : List ConLeche.NestHole) (hi : Nat) (us : LsIdx)
    (usP : List Level) (ds : List EIdx) (dsP : List Expr) (names : List NIdx)
    (namesP : List ConLeche.Name) (holes : List EIdx) (holesP : List Expr)
    (hds : ∀ d ∈ dsP, Expr.WScoped hi d) (hholes : ∀ x ∈ holesP, Expr.WScoped hi x)
    (hlen : namesP.length ≤ holesP.length) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
      (ns : Arena.NestState) (nsP : ConLeche.NestState)
      (outs : List (List Arena.NestFieldKind × EIdx))
      (outsP : List (List ConLeche.NestFieldKind × Expr)),
      (∀ c ∈ csP, c.1.type.hasFvar = false) →
      CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
          dProg st prog = some progP ∧ denoteLs st.lss us = some usP ∧
          Frontend.denoteEList st ds = some dsP ∧
          Frontend.denoteNList st.ns names = some namesP ∧
          Frontend.denoteEList st holes = some holesP ∧ dCtors st cs = some csP ∧
          dState st ns = some nsP ∧ outs.mapM (dOut st) = some outsP)
        (Arena.nestCtors μ fe ctx root fuel prog hi us ds names holes cs ns outs)
        (fun st r v => r.1.mapM (dOut st) = some (outsP ++ v.1) ∧ dState st r.2 = some v.2 ∧
          ∀ o ∈ v.1, Expr.WScoped hi o.2)
        (ConLeche.nestCtors ctxP (fueledOpsM μ) env rec progP hi usP dsP namesP holesP csP
          nsP) := by
  intro cs
  induction cs with
  | nil =>
    intro csP ns nsP outs outsP hcs s₀ s' r hok hp hrun
    obtain ⟨-, -, -, -, -, -, hcs', hns, houts⟩ := hp
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs'
    subst hcs'
    rw [Arena.nestCtors] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨CoreStep.refl hok, ([], nsP), ⟨by simpa using houts, hns, fun _ h => nomatch h⟩, ?_⟩
    simp only [ConLeche.nestCtors]
    exact FOk.pure _
  | cons c cs ih =>
    intro csP ns nsP outs outsP hcs s₀ s' r hok hp hrun
    obtain ⟨hctx, hprog, hus, hds', hnames, hholes', hcs', hns, houts⟩ := hp
    obtain ⟨cv, nF⟩ := c
    simp only [dCtors, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hcs'
    cases hc1 : dCtor s₀.store (cv, nF) with
    | none => rw [hc1] at hcs'; simp at hcs'
    | some cP =>
    cases hcs1 : cs.mapM (dCtor s₀.store) with
    | none => rw [hc1, hcs1] at hcs'; simp at hcs'
    | some csP' =>
    rw [hc1, hcs1] at hcs'
    simp only [Option.bind_some, Option.some.injEq] at hcs'
    subst hcs'
    simp only [dCtor, Option.map_eq_some_iff] at hc1
    obtain ⟨cvP, hcvP, rfl⟩ := hc1
    obtain ⟨hcvn, hcvl, hcvt⟩ := denoteCV_inv hcvP
    obtain ⟨hcnames, hcnP, -, -, -, -⟩ := dCtx_fields hctx
    have hcl : cvP.type.hasFvar = false := hcs _ List.mem_cons_self
    rw [Arena.nestCtors] at hrun
    dsimp only at hrun
    have hnod := nameNodup_spec hok.state.wf _ _ hcvl
    by_cases hn : (!nameNodup cv.levelParams) = true
    · rw [if_pos hn] at hrun; exact absurd hrun (fun hc => failOk hc)
    rw [if_neg hn] at hrun
    have hnod' : ConLeche.Name.nodup cvP.levelParams = true := by
      rw [← hnod]; simpa using hn
    -- the level instantiation
    obtain ⟨cty, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨c1, hcty⟩ := instLPFast_cstep hok hcvl hus hcvt h1
    -- the crest
    obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨p2, ho⟩ := nestCrest_spec names namesP us usP ds dsP holes holesP cty _ s₁ s₂ o
      c1.ok.state c1.ok.pins ⟨denoteNListE_ext c1.ext _ _ hnames, denoteLs_ext hus c1.ext,
        denoteEList_ext c1.ext _ _ hds', denoteEList_ext c1.ext _ _ hholes', hcty⟩ h3
    have c2 := c1.trans (p2.toCore c1.ok)
    cases o with
    | none => exact absurd h4 (fun hc => failOk hc)
    | some crest =>
    obtain ⟨crestP, hcrestP, hcrest⟩ := ho
    dsimp only at h4
    have hwc : Expr.WScoped hi crestP :=
      WScoped_nestCrest (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcl) hlen
        (fun x hx => (List.mem_append.mp hx).elim (hds x) (hholes x)) hcrestP
    -- typed at the frame's depth
    obtain ⟨ty, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨c3, tyP, hty, hwty, hFty⟩ := infer_crun hk henv c2.ok hcrest hwc h5
    obtain ⟨u, s₄, h7, h8⟩ := bindOk h6
    obtain ⟨c4, uP, hu, hFu⟩ := ensureSort_crun hk henv c3.ok hty hwty h7
    have c14 := c2.trans (c3.trans c4)
    -- the fields, at the fuel `root` picks
    rw [dite_bind_AM] at h8
    obtain ⟨fc, s₄', h9, h9a⟩ := bindOk h8
    have hcr4 : denoteE s₄.store crest = some crestP := denote_ext hcrest (c3.ext.trans c4.ext)
    have hfld : PStep s₄ s₄' ∧ fc = (if root then whnfWalkFuel crestP else fuel) := by
      cases root with
      | true =>
        simp only [↓reduceIte] at h9
        obtain ⟨p, hfc⟩ := whnfWalkFuel_spec crest crestP s₄ s₄' fc c4.ok.state hcr4 h9
        exact ⟨p, by simpa using hfc⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h9
        obtain ⟨rfl, rfl⟩ := pureOk h9
        exact ⟨PStep.refl c4.ok.state, by simp⟩
    obtain ⟨p4', hfc⟩ := hfld
    subst hfc
    obtain ⟨q, s₅, h9', h10⟩ := bindOk h9a
    have c4' := c14.trans (p4'.toCore c14.ok)
    have hx04 := c14.ext.trans p4'.ext
    obtain ⟨c5, vf, ⟨hks, hnds, hcur, hns2, hwnds, hwcur⟩, hFf⟩ :=
      nestFields_spec (hps crestP) prog progP hi
        (.invalid "nested positivity: invalid nested inductive datatype, its constructor type does not bind its fields (official: ill-formed constructor)")
        nF 0 crest crestP ns nsP [] [] [] (by simpa using hwc) s₄' s₅ q c4'.ok
        ⟨dCtx_ext _ hx04 _ _ hctx, dProg_ext hx04 _ _ hprog, denote_ext hcr4 p4'.ext,
          dState_ext hx04 _ _ hns, rfl⟩ h9'
    obtain ⟨ks, nds, cur, ns2⟩ := q
    simp only [List.map_nil, List.nil_append] at hks hnds
    dsimp only at h10 hks hnds hcur hns2
    -- the walked telescope, closed
    obtain ⟨closed, s₆, h11, h12⟩ := bindOk h10
    obtain ⟨p6, hclosed⟩ := closeTelescope_spec nds vf.2.1 hi cur vf.2.2.1 s₅ s₆ closed
      c5.ok.state ⟨hnds, hcur⟩ h11
    -- U4
    obtain ⟨u4, s₇, h13, h14⟩ := bindOk h12
    obtain ⟨p7, hu4⟩ := anyM_pstep (fun _ st => denoteE st closed =
        some (ConLeche.closeTelescope vf.2.1 hi vf.2.2.1))
      (g := fun i => vf.1.getD i .ordinary != .ordinary &&
        ConLeche.structUsedLater (ConLeche.closeTelescope vf.2.1 hi vf.2.2.1) 0 i)
      (fun hx h => denote_ext h hx)
      (fun i s₀ s' b hok' hq hrun' => by
        rw [u4_kind, hks] at hrun'
        cases hkd : (vf.1.getD i .ordinary != .ordinary) with
        | true =>
          rw [hkd] at hrun'
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun'
          obtain ⟨p, hb⟩ := structUsedLater_spec closed _ 0 i s₀ s' b hok' hq hrun'
          exact ⟨p, by simp only [RV] at hb; rw [hb, Bool.true_and]⟩
        | false =>
          rw [hkd] at hrun'
          simp only [Bool.not_false, ↓reduceIte] at hrun'
          obtain ⟨rfl, rfl⟩ := pureOk hrun'
          exact ⟨PStep.refl hok', by rw [Bool.false_and]⟩)
      (List.range nF) s₆ s₇ u4 p6.ok (fun _ _ => hclosed) h13
    cases u4 with
    | true => simp only [↓reduceIte] at h14; exact absurd h14 (fun hc => failOk hc)
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h14
    -- the result
    have hx57 := p6.ext.trans p7.ext
    have hcur7 : denoteE s₇.store cur = some vf.2.2.1 := denote_ext hcur hx57
    obtain ⟨rh, s₈, h15, h16⟩ := bindOk h14
    obtain ⟨p8, hrh⟩ := nestResHead_spec cur vf.2.2.1 s₇ s₈ rh p7.ok hcur7 h15
    simp only [RV] at hrh
    cases rh with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, Bool.not_false] at h16
      exact absurd h16 (fun hc => failOk hc)
    | true =>
    simp only [↓reduceIte] at h16
    obtain ⟨args, s₉, h17, h18⟩ := bindOk h16
    obtain ⟨hs9, hargs⟩ := getAppArgs_run p8.ok (denote_ext hcur7 p8.ext) h17
    rw [hs9] at h18
    obtain ⟨occ, s₁₀, h19, h20⟩ := bindOk h18
    have hx08 := c4'.ext.trans (c5.ext.trans (hx57.trans p8.ext))
    obtain ⟨p10, hocc⟩ := anyM_E_pstep (fun st => Frontend.denoteNList st.ns ctx.names =
        some ctxP.names)
      (fun hx h => denoteNListE_ext hx _ _ h)
      (fun e eP s₀ s' b hok' hq hd hrun' =>
        nestOcc_spec ctx.names ctxP.names ctx.nP hi e eP s₀ s' b hok' ⟨hq, hd⟩ hrun')
      args _ s₈ s₁₀ occ p8.ok (denoteNListE_ext hx08 _ _ hcnames) hargs h19
    simp only [pure_bind] at h20
    cases occ with
    | true => simp only [Bool.not_true, Bool.not_false, ↓reduceIte] at h20
              exact absurd h20 (fun hc => failOk hc)
    | false =>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h20
    -- the record
    have hx010 := hx08.trans p10.ext
    have hx510 := hx57.trans (p8.ext.trans p10.ext)
    obtain ⟨nf, s₁₁, h21, h22⟩ := bindOk h20
    have c10 := c4'.trans (c5.trans ((p6.trans (p7.trans (p8.trans p10))).toCore c5.ok))
    obtain ⟨p11, hnf⟩ := nestCtorNf_spec ctx prog us ds cv closed env.find? ctxP progP usP dsP
      cvP (ConLeche.closeTelescope vf.2.1 hi vf.2.2.1) s₁₀ s₁₁ nf c10.ok.state c10.ok.pins
      ⟨dCtx_ext _ hx010 _ _ hctx, dProg_ext hx010 _ _ hprog, denoteLs_ext hus hx010,
        denoteEList_ext hx010 _ _ hds', denoteCV_ext hcvP hx010,
        denote_ext hclosed (p7.ext.trans (p8.ext.trans p10.ext))⟩ h21
    have c11 := c10.trans (p11.toCore c10.ok)
    have hx511 := hx510.trans p11.ext
    have hx011 := hx010.trans p11.ext
    have hwN : Expr.WScoped hi (ConLeche.closeTelescope vf.2.1 hi vf.2.2.1) :=
      Cached.closeTelescope_wscoped vf.2.1 hi vf.2.2.1
        (fun k nd hk => by simpa using hwnds k nd hk) (by simpa using hwcur)
    obtain ⟨c12, vr, ⟨hvr1, hvr2, hvr3⟩, hFr⟩ := ih csP' _
      ({ keys := vf.2.2.2.keys, active := vf.2.2.2.active, ctorNfs := vf.2.2.2.ctorNfs.push (ConLeche.nestCtorNf ctxP progP hi usP dsP cvP vf.2.1 vf.2.2.1) } : ConLeche.NestState)
      (outs ++ [(ks, closed)]) (outsP ++ [(vf.1, ConLeche.closeTelescope vf.2.1 hi vf.2.2.1)])
      (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) s₁₁ s' r c11.ok
      ⟨dCtx_ext _ hx011 _ _ hctx, dProg_ext hx011 _ _ hprog, denoteLs_ext hus hx011,
        denoteEList_ext hx011 _ _ hds', denoteNListE_ext hx011 _ _ hnames,
        denoteEList_ext hx011 _ _ hholes', dCtors_ext hx011 _ _ hcs1,
        dState_push (dState_ext hx511 _ _ hns2) hnf,
        mapM_option_append (dOut_ext.list hx011 _ _ houts)
          (by simp [dOut, denote_ext hclosed (p7.ext.trans (p8.ext.trans (p10.ext.trans
            p11.ext))), hks])⟩ h22
    refine ⟨c11.trans c12, ((vf.1, ConLeche.closeTelescope vf.2.1 hi vf.2.2.1) :: vr.1, vr.2),
      ⟨by rw [hvr1]; simp, hvr2, fun o ho => ?_⟩, ?_⟩
    · rcases List.mem_cons.mp ho with rfl | ho
      · exact hwN
      · exact hvr3 o ho
    · have hu4' : ((List.range nF).any fun i => vf.1.getD i .ordinary != .ordinary &&
          ConLeche.structUsedLater (ConLeche.closeTelescope vf.2.1 hi vf.2.2.1) 0 i) = false :=
        hu4.symm
      have hres' : (ConLeche.nestResHead vf.2.2.1 &&
          vf.2.2.1.getAppArgs.all fun x => !Expr.nestOcc ctxP.names ctxP.nP hi x) = true := by
        rw [← hrh, ← List.not_any_eq_all_not, ← hcnP, ← hocc]; rfl
      simp only [ConLeche.nestCtors, if_pos hnod', hcrestP]
      refine FOk.bind FOk.unwrapOr ?_
      refine FOk.bind hFty ?_
      refine FOk.bind hFu ?_
      rw [hrec crestP]
      refine FOk.bind hFf ?_
      simp only [hu4', hres', Bool.false_eq_true, ↓reduceIte]
      exact FOk.bind hFr (FOk.pure _)

end Ctors

section Frame

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: none — `List.mapIdx` of an index-blind function is `map`. -/
theorem mapIdx_blind {α β : Type} (f : α → β) (l : List α) :
    l.mapIdx (fun _ a => f a) = l.map f := by
  apply List.ext_getElem <;> simp

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame —
the twin's frame with its head's name as one bind (the `do` elaborator puts
the continuation in a join point). -/
theorem nestFrame_eq (mode : CheckMode) (fe : IFEnv) (ctx : Arena.NestCtx) (fuel : Nat)
    (prog : List Arena.NestHole) (hi : Nat) (us : LsIdx) (ds : List EIdx) (nPc : Nat)
    (grp : List (NIdx × EIdx)) (ns : Arena.NestState) :
    Arena.nestFrame mode fe ctx fuel prog hi us ds nPc grp ns = (do
      let hn ← (match grp with
        | [] => internNNode .anonymous
        | (c, _) :: _ => pure c : AM NIdx)
      let hc ← internConstE hn us
      let app ← Arena.mkAppN hc ds
      let _ ← Arena.inferTypeCore mode fe Arena.checkFuel hi app
      let prog2 := prog ++ grp.map fun (c, _) =>
        ({ key := ⟨c, us, ds⟩, base := hi } : Arena.NestHole)
      let names := grp.map (·.1)
      let ctors ← Arena.nestGroupCtors fe nPc names []
      let holes ← grp.zipIdx.mapM fun ((_, ty), i) => internFVarE (hi + i) ty
      let (_, ns2) ← Arena.nestCtors mode fe ctx false fuel prog2 (hi + grp.length) us ds
        names holes ctors ns []
      pure ns2) := by
  rw [Arena.nestFrame.eq_def]
  cases grp <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1327-1351 nestFrame
**A container frame** (con-leche's `nestFrameS_sim`): the instantiation typed
at the frame's depth, the group's constructors walked at the enclosing walk's
fuel, with the frame's holes above `hi`. -/
theorem nestFrame_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP) {fuel : Nat}
    (ih : NestPosSpec μ env fe ctx ctxP fuel)
    (prog : List Arena.NestHole) (progP : List ConLeche.NestHole) (hi : Nat) (us : LsIdx)
    (usP : List Level) (ds : List EIdx) (dsP : List Expr) (nPc : Nat)
    (grp : List (NIdx × EIdx)) (grpP : List (ConLeche.Name × Expr)) (ns : Arena.NestState)
    (nsP : ConLeche.NestState)
    (hds : ∀ d ∈ dsP, Expr.WScoped hi d) (hg : ∀ x ∈ grpP, Expr.WScoped hi x.2) :
    CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
        dProg st prog = some progP ∧ denoteLs st.lss us = some usP ∧
        Frontend.denoteEList st ds = some dsP ∧ dGrp st grp = some grpP ∧
        dState st ns = some nsP)
      (Arena.nestFrame μ fe ctx fuel prog hi us ds nPc grp ns)
      (fun st r v => dState st r = some v)
      (ConLeche.nestFrame ctxP (fueledOpsM μ) env (ConLeche.nestPos (fueledOpsM μ) env ctxP fuel)
        progP hi usP dsP nPc grpP nsP) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hctx, hprog, hus, hds', hgrp, hns⟩ := hp
  obtain ⟨-, -, hfind, -, -, -⟩ := dCtx_fields hctx
  rw [nestFrame_eq] at hrun
  -- the head's name
  obtain ⟨hn, s₁, h1, h2⟩ := bindOk hrun
  have hhn : PStep s₀ s₁ ∧ denoteN s₁.store.ns hn = some (grpP.headD default).1 := by
    cases grp with
    | nil =>
      simp only [dGrp, List.mapM_nil, Option.pure_def, Option.some.injEq] at hgrp
      subst hgrp
      dsimp only at h1
      obtain ⟨p, hd⟩ := internNNode_run hok.state
        (by intro c hc; simp [NNodeView.children] at hc) h1
      exact ⟨p, by rw [hd]; rfl⟩
    | cons x grp' =>
      dsimp only at h1
      obtain ⟨hr, hs⟩ := pureOk h1
      subst hr
      rw [hs]
      simp only [dGrp, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hgrp
      cases hx : dGE s₀.store x with
      | none => rw [hx] at hgrp; simp at hgrp
      | some y =>
      cases hxs : grp'.mapM (dGE s₀.store) with
      | none => rw [hx, hxs] at hgrp; simp at hgrp
      | some ys =>
      rw [hx, hxs] at hgrp
      simp only [Option.bind_some, Option.some.injEq] at hgrp
      subst hgrp
      simp only [dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
      obtain ⟨cP, hcP, tyP, htyP, rfl⟩ := hx
      exact ⟨PStep.refl hok.state, hcP⟩
  obtain ⟨p1, hhn'⟩ := hhn
  have c1 := p1.toCore hok
  obtain ⟨hc', s₂, h3, h4⟩ := bindOk h2
  obtain ⟨p2, hc2⟩ := internConstE_run c1.ok.state hhn' (denoteLs_ext hus p1.ext) h3
  obtain ⟨app, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨p3, happ⟩ := mkAppN_run ds dsP p2.ok hc2
    (denoteEList_ext (p1.ext.trans p2.ext) _ _ hds') h5
  -- the instantiation, typed
  obtain ⟨tyA, s₄, h7, h8⟩ := bindOk h6
  have c3 := c1.trans ((p2.trans p3).toCore c1.ok)
  have hwapp : Expr.WScoped hi (Expr.mkAppN (.const (grpP.headD default).1 usP) dsP) :=
    Expr.WScoped.mkAppN (by simp [Expr.WScoped]) hds
  obtain ⟨c4, tyP, -, -, hFty⟩ := infer_crun hk henv c3.ok happ hwapp h7
  dsimp only at h8
  -- the group's constructors
  obtain ⟨ctors, s₅, h9, h10⟩ := bindOk h8
  have hx04 : Ext s₀.store s₄.store := c3.ext.trans c4.ext
  have hgrp4 := dGrp_ext hx04 _ _ hgrp
  obtain ⟨p5, vc, hvc, hFc, hvcl⟩ := nestGroupCtors_spec ctxP hfind hc nPc _ _ [] []
    s₄ s₅ ctors c4.ok.state ⟨c4.ok.ienv.toS, dGrp_names hgrp4, rfl⟩ h9
  simp only [List.nil_append] at hvc
  -- the frame's holes
  obtain ⟨holes, s₆, h11, h12⟩ := bindOk h10
  obtain ⟨p6, hholes⟩ := frameHoles_run hi (fun c ty i => rfl) grp grpP 0 s₅ s₆ holes p5.ok
    (dGrp_ext p5.ext _ _ hgrp4) h11
  have hholesEq : ((grpP.zipIdx 0).map fun p => Expr.fvar (hi + p.2) p.1.2) =
      grpP.mapIdx (fun i (x : ConLeche.Name × Expr) => Expr.fvar (hi + i) x.2) := by
    rw [List.mapIdx_eq_zipIdx_map]
  rw [hholesEq] at hholes
  -- the constructors walked
  obtain ⟨q, s₇, h13, h14⟩ := bindOk h12
  have hlenG : grp.length = grpP.length := (mapM_option_length hgrp).symm
  rw [hlenG] at h13
  have hx06 := hx04.trans (p5.ext.trans p6.ext)
  have c6 := c3.trans (c4.trans ((p5.trans p6).toCore c4.ok))
  have hprog2 : dProg s₆.store (prog ++ grp.map fun (x : NIdx × EIdx) =>
      ({ key := ⟨x.1, us, ds⟩, base := hi } : Arena.NestHole)) =
      some ((grpP.mapIdx fun _ (x : ConLeche.Name × Expr) =>
        ({ key := ⟨x.1, usP, dsP⟩, base := hi } : ConLeche.NestHole)).reverse ++ progP) := by
    rw [mapIdx_blind (fun (x : ConLeche.Name × Expr) =>
      ({ key := ⟨x.1, usP, dsP⟩, base := hi } : ConLeche.NestHole))]
    exact dProg_append (dProg_ext hx06 _ _ hprog)
      (dHoles_grp (denoteLs_ext hus hx06) (denoteEList_ext hx06 _ _ hds') hi
        (dGrp_ext hx06 _ _ hgrp))
  obtain ⟨c7, v, ⟨-, hv2, -⟩, hFv⟩ := nestCtors_spec hk henv false fuel
    (fun _ => ConLeche.nestPos (fueledOpsM μ) env ctxP fuel) (fun _ => by simp)
    (fun _ => by simpa using ih) _ _ (hi + grpP.length) us usP ds dsP _ _ holes _
    (fun d hd => Expr.WScoped.mono (Nat.le_add_right _ _) (hds d hd))
    (Cached.frameHoles_wscoped hg) (by simp) ctors vc ns nsP [] [] hvcl s₆ s₇ q c6.ok
    ⟨dCtx_ext _ hx06 _ _ hctx, hprog2, denoteLs_ext hus hx06, denoteEList_ext hx06 _ _ hds',
      dGrp_names (dGrp_ext (p5.ext.trans p6.ext) _ _ hgrp4), hholes,
      dCtors_ext p6.ext _ _ hvc, dState_ext hx06 _ _ hns, rfl⟩ h13
  obtain ⟨o, ns2⟩ := q
  dsimp only at h14
  obtain ⟨rfl, rfl⟩ := pureOk h14
  refine ⟨c6.trans c7, v.2, hv2, ?_⟩
  simp only [ConLeche.nestFrame]
  exact FOk.bind hFty (FOk.bind hFc (FOk.bind hFv (FOk.pure _)))

end Frame

section Cont

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1359-1382 nestContNew
An instantiation's frame (con-leche's `nestContNewS_sim`): the group grown,
the frame walked with the group in progress, the group cached when its
parameters mention no frame hole. -/
theorem nestContNew_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP) {fuel : Nat}
    (ih : NestPosSpec μ env fe ctx ctxP fuel)
    (prog : List Arena.NestHole) (progP : List ConLeche.NestHole) (kb : Nat) (n : NIdx)
    (nP : ConLeche.Name) (us : LsIdx) (usP : List Level) (ds : List EIdx) (dsP : List Expr)
    (nPc : Nat) (cty : EIdx) (ctyP : Expr) (ns : Arena.NestState) (nsP : ConLeche.NestState)
    (hds : ∀ d ∈ dsP, Expr.WScoped (ctxP.hiAt progP.length) d)
    (hni : ∀ d, (∀ y ∈ dsP, Expr.WScoped d y) → Expr.WScoped d ctyP) :
    CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
        dProg st prog = some progP ∧ denoteN st.ns n = some nP ∧
        denoteLs st.lss us = some usP ∧ Frontend.denoteEList st ds = some dsP ∧
        denoteE st cty = some ctyP ∧ dState st ns = some nsP)
      (Arena.nestContNew μ fe ctx fuel prog kb n us ds nPc cty ns)
      (fun st r v => v.1 = kindOf r.1 ∧ dState st r.2 = some v.2)
      (ConLeche.nestContNew ctxP (fueledOpsM μ) env
        (ConLeche.nestPos (fueledOpsM μ) env ctxP fuel) progP kb nP usP dsP nPc ctyP nsP) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hctx, hprog, hn, hus, hds', hcty, hns⟩ := hp
  obtain ⟨-, -, hfind, -, -, -⟩ := dCtx_fields hctx
  rw [Arena.nestContNew.eq_def] at hrun
  -- the walk stack
  obtain ⟨wp, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hwp⟩ := nestWalkStack_spec ctx prog ds dsP s₀ s₁ wp hok.state hds' h1
  simp only [RV, hiAt_eq hctx] at hwp
  have hwpP : dProg s₀.store wp = some (ConLeche.nestWalkStack ctxP progP dsP) := by
    rw [hwp]; simp only [ConLeche.nestWalkStack]
    split
    · rfl
    · exact hprog
  have hwpl : wp.length = (ConLeche.nestWalkStack ctxP progP dsP).length :=
    dProg_length hwpP
  have hdsw : ∀ d ∈ dsP,
      Expr.WScoped (ctxP.hiAt (ConLeche.nestWalkStack ctxP progP dsP).length) d := by
    unfold ConLeche.nestWalkStack; split
    · rename_i hfree
      intro x hx
      exact ConLeche.WScoped.of_fvarsBelow (hds x hx)
        (Expr.fvarB_le (by simpa using List.all_eq_true.mp hfree x hx))
    · exact hds
  have c1 := p1.toCore hok
  -- the group
  obtain ⟨grp, s₂, h3, h4⟩ := bindOk h2
  have hmates := nestFrameMates_rel c1.ok.state c1.ok.ienv ctxP hfind (denoteN_ext hn p1.ext)
  rw [hiAt_eq (dCtx_ext _ p1.ext _ _ hctx), hwpl] at h3
  obtain ⟨c2, grpV, ⟨hgrp, hgs⟩, hFg⟩ := nestGrowGroup_spec hc ctx _ us usP ds dsP _ _
    [(n, cty)] [(nP, ctyP)]
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hni)
    s₁ s₂ grp c1.ok ⟨dCtx_ext _ p1.ext _ _ hctx, denoteLs_ext hus p1.ext,
      denoteEList_ext p1.ext _ _ hds', hmates,
      by simp [dGrp, dGE, denoteN_ext hn p1.ext, denote_ext hcty p1.ext]⟩ h3
  have hx02 := p1.ext.trans c2.ext
  obtain ⟨hk1, hk2, hk3⟩ := dState_inv (dState_ext hx02 _ _ hns)
  -- the frame
  obtain ⟨ns2, s₃, h5, h6⟩ := bindOk h4
  rw [hiAt_eq (dCtx_ext _ hx02 _ _ hctx), hwpl] at h5
  have c12 := c1.trans c2
  obtain ⟨c3, nsP2, hns2, hFf⟩ := nestFrame_spec hk henv hc ih wp _ _ us usP ds dsP nPc grp
    grpV _ (ConLeche.NestState.mk nsP.keys
      (grpV.map (fun p => (⟨p.1, usP, dsP⟩ : ConLeche.NestKey)) ++ nsP.active) nsP.ctorNfs)
    hdsw (fun x hx => hgs x hx _ hdsw) s₂ s₃ ns2 c12.ok
    ⟨dCtx_ext _ hx02 _ _ hctx, dProg_ext hx02 _ _ hwpP, denoteLs_ext hus hx02,
      denoteEList_ext hx02 _ _ hds', hgrp,
      dState_mk hk1 (mapM_option_append (dKeys_grp (denoteLs_ext hus hx02)
        (denoteEList_ext hx02 _ _ hds') hgrp) hk2) hk3⟩ h5
  -- the cache
  obtain ⟨closed, s₄, h7, h8⟩ := bindOk h6
  have hx03 := hx02.trans c3.ext
  obtain ⟨p4, hcl⟩ := closedAll_spec (ctx.hiAt 0) ds dsP s₃ s₄ closed c3.ok.state
    (denoteEList_ext hx03 _ _ hds') h7
  simp only [RV, hiAt_eq hctx] at hcl
  subst hcl
  obtain ⟨rfl, rfl⟩ := pureOk h8
  have c4 := c12.trans (c3.trans (p4.toCore c3.ok))
  obtain ⟨hn1, hn2, hn3⟩ := dState_inv (dState_ext p4.ext _ _ hns2)
  refine ⟨c4, (.nested (kb != 0), ConLeche.NestState.mk
      (if dsP.all (fun x => decide (x.fvarB ≤ ctxP.hiAt 0)) then
        ConLeche.nestAcceptGroup usP dsP grpV nsP2.keys else nsP2.keys)
      nsP.active nsP2.ctorNfs), ⟨rfl, ?_⟩, ?_⟩
  · refine dState_mk ?_ (by
      obtain ⟨-, ha, -⟩ := dState_inv (dState_ext (hx03.trans p4.ext) _ _ hns); exact ha) hn3
    by_cases hcl : (dsP.all fun x => decide (x.fvarB ≤ ctxP.hiAt 0)) = true
    · rw [if_pos hcl, if_pos hcl]
      exact nestAcceptGroup_denote c4.ok.state.wf (denoteLs_ext hus (hx03.trans p4.ext))
        (denoteEList_ext (hx03.trans p4.ext) _ _ hds') grp grpV _ _
        (dGrp_names (dGrp_ext (c3.ext.trans p4.ext) _ _ hgrp)) hn1
    · rw [if_neg hcl, if_neg hcl]
      exact hn1
  · simp only [ConLeche.nestContNew]
    exact FOk.bind hFg (FOk.bind hFf (FOk.pure _))

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1384-1404 nestContKey
The instantiation met (con-leche's `nestContKeyS_sim`): in progress, a cache
hit, or a new frame — the same verdict. -/
theorem nestContKey_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP) {fuel : Nat}
    (ih : NestPosSpec μ env fe ctx ctxP fuel)
    (prog : List Arena.NestHole) (progP : List ConLeche.NestHole) (kb : Nat) (n : NIdx)
    (nP : ConLeche.Name) (us : LsIdx) (usP : List Level) (ds : List EIdx) (dsP : List Expr)
    (nPc : Nat) (cty : EIdx) (ctyP : Expr) (ns : Arena.NestState) (nsP : ConLeche.NestState)
    (hds : ∀ d ∈ dsP, Expr.WScoped (ctxP.hiAt progP.length) d)
    (hni : ∀ d, (∀ y ∈ dsP, Expr.WScoped d y) → Expr.WScoped d ctyP) :
    CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
        dProg st prog = some progP ∧ denoteN st.ns n = some nP ∧
        denoteLs st.lss us = some usP ∧ Frontend.denoteEList st ds = some dsP ∧
        denoteE st cty = some ctyP ∧ dState st ns = some nsP)
      (Arena.nestContKey μ fe ctx fuel prog kb n us ds nPc cty ns)
      (fun st r v => v.1 = kindOf r.1 ∧ dState st r.2 = some v.2)
      (ConLeche.nestContKey ctxP (fueledOpsM μ) env
        (ConLeche.nestPos (fueledOpsM μ) env ctxP fuel) progP kb nP usP dsP nPc ctyP nsP) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hctx, hprog, hn, hus, hds', hcty, hns⟩ := hp
  rw [Arena.nestContKey.eq_def] at hrun
  dsimp only at hrun
  have hkey : dKey s₀.store ⟨n, us, ds⟩ = some ⟨nP, usP, dsP⟩ := by
    simp [dKey, hn, hus, hds']
  obtain ⟨hk1, hk2, hk3⟩ := dState_inv hns
  have hact := contains_key_eq hok.state.wf hkey hk2
  by_cases ha : ns.active.contains ⟨n, us, ds⟩ = true
  · rw [if_pos ha] at hrun; exact absurd hrun (fun hc => failOk hc)
  rw [if_neg ha] at hrun
  have ha' : nsP.active.contains ⟨nP, usP, dsP⟩ = false := by
    rw [← hact]; simpa using ha
  obtain ⟨closed, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hcl⟩ := closedAll_spec (ctx.hiAt 0) ds dsP s₀ s₁ closed hok.state hds' h1
  simp only [RV, hiAt_eq hctx] at hcl
  subst hcl
  have hkeys : ns.keys.contains ⟨n, us, ds⟩ = nsP.keys.contains ⟨nP, usP, dsP⟩ := by
    rw [← Array.contains_toList, ← Array.contains_toList]
    exact contains_key_eq hok.state.wf hkey hk1
  rw [hkeys] at h2
  simp only [ConLeche.nestContKey, ha', Bool.false_eq_true, ↓reduceIte]
  by_cases hhit : ((dsP.all fun x => decide (x.fvarB ≤ ctxP.hiAt 0)) &&
      nsP.keys.contains ⟨nP, usP, dsP⟩) = true
  · rw [if_pos hhit] at h2
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨p1.toCore hok, (.nested (kb != 0), nsP), ⟨rfl, dState_ext p1.ext _ _ hns⟩, ?_⟩
    rw [if_pos hhit]
    exact FOk.pure _
  · rw [if_neg hhit] at h2
    have c1 := p1.toCore hok
    obtain ⟨c2, v, hv, hF⟩ := nestContNew_spec hk henv hc ih prog progP kb n nP us usP ds dsP
      nPc cty ctyP ns nsP hds hni s₁ s' r c1.ok
      ⟨dCtx_ext _ p1.ext _ _ hctx, dProg_ext p1.ext _ _ hprog, denoteN_ext hn p1.ext,
        denoteLs_ext hus p1.ext, denoteEList_ext p1.ext _ _ hds', denote_ext hcty p1.ext,
        dState_ext p1.ext _ _ hns⟩ h2
    refine ⟨c1.trans c2, v, hv, ?_⟩
    rw [if_neg hhit]
    exact hF

end Cont

section ContCase

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1406-1440 nestCont
(the parameters' check) — no loose bound variable, no frame hole past the
walk's depth, at each parameter. -/
theorem paramsLocal_spec (hp : Nat) (ds : List EIdx) (dsP : List Expr) :
    PSpec (fun st => Frontend.denoteEList st ds = some dsP)
      (ds.allM fun x => do
        let bb ← bvarB coreWalkFuel x
        if bb != 0 then pure false
        else do
          let fb ← fvarB coreWalkFuel x
          pure (decide (fb ≤ hp)))
      (RV (dsP.all fun x => x.bvarB == 0 && decide (x.fvarB ≤ hp))) := by
  intro s₀ s' r hok hd hrun
  exact allM_E_pstep (fun _ => True) (fun _ _ => trivial)
    (fun e eP s₀ s' b hok _ hd hrun => by
      obtain ⟨bb, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨p1, -, rfl⟩ := bvarB_pstep hok hd h1
      by_cases hb : (eP.bvarB != 0) = true
      · rw [if_pos hb] at h2
        obtain ⟨rfl, rfl⟩ := pureOk h2
        refine ⟨p1, ?_⟩
        simp only [bne_iff_ne, ne_eq] at hb
        simp [hb]
      · rw [if_neg hb] at h2
        obtain ⟨fb, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨p2, rfl⟩ := fvarB_pstep p1.ok (denote_ext hd p1.ext) h3
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨p1.trans p2, ?_⟩
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hb
        simp [hb])
    ds dsP s₀ s' r hok trivial hd hrun

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1406-1440 nestCont
**The container case** (con-leche's `nestContS_sim`): the container's checks,
its former, then the instantiation (`nestContKey_spec`). -/
theorem nestCont_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP) {fuel : Nat}
    (ih : NestPosSpec μ env fe ctx ctxP fuel)
    (prog : List Arena.NestHole) (progP : List ConLeche.NestHole) (kb : Nat) (n : NIdx)
    (nP : ConLeche.Name) (us : LsIdx) (usP : List Level) (args : List EIdx)
    (argsP : List Expr) (ns : Arena.NestState) (nsP : ConLeche.NestState) {dep : Nat}
    (hargs : ∀ a ∈ argsP, Expr.WScoped dep a) :
    CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
        dProg st prog = some progP ∧ denoteN st.ns n = some nP ∧
        denoteLs st.lss us = some usP ∧ Frontend.denoteEList st args = some argsP ∧
        dState st ns = some nsP)
      (Arena.nestCont μ fe ctx fuel prog kb n us args ns)
      (fun st r v => v.1 = kindOf r.1 ∧ dState st r.2 = some v.2)
      (ConLeche.nestCont ctxP (fueledOpsM μ) env
        (ConLeche.nestPos (fueledOpsM μ) env ctxP fuel) progP kb nP usP argsP nsP) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hctx, hprog, hn, hus, hargs', hns⟩ := hp
  obtain ⟨hcnames, hcnP, hfind, -, -, -⟩ := dCtx_fields hctx
  have hhp : ctx.hiAt prog.length = ctxP.hiAt progP.length := by
    rw [hiAt_eq hctx, dProg_length hprog]
  rw [Arena.nestCont.eq_def] at hrun
  dsimp only at hrun
  -- the container
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := nestContainer_spec ctxP hfind n nP s₀ s₁ o hok.state
    ⟨hok.ienv.toS, hn⟩ h1
  cases o with
  | none => exact absurd h2 (fun hc => failOk hc)
  | some q =>
  obtain ⟨nPc, cs⟩ := q
  obtain ⟨qP, hqP, hq1, -⟩ := ho
  dsimp only at h2 hq1
  subst hq1
  have hlenA := PW.denoteEList_length hargs'
  by_cases hl : args.length < qP.1
  · rw [if_pos hl] at h2; exact absurd h2 (fun hc => failOk hc)
  rw [if_neg hl] at h2
  -- the indices
  obtain ⟨b, s₂, h3, h4⟩ := bindOk h2
  have hargs1 := denoteEList_ext p1.ext _ _ hargs'
  obtain ⟨p2, hb⟩ := anyM_E_pstep (fun st => Frontend.denoteNList st.ns ctx.names =
      some ctxP.names)
    (fun hx h => denoteNListE_ext hx _ _ h)
    (fun e eP s₀ s' b hok' hq hd hrun' =>
      nestOcc_spec ctx.names ctxP.names ctx.nP _ e eP s₀ s' b hok' ⟨hq, hd⟩ hrun')
    _ _ s₁ s₂ b p1.ok (denoteNListE_ext p1.ext _ _ hcnames) (denoteEList_drop' qP.1 hargs1) h3
  cases b with
  | true => simp only [↓reduceIte] at h4; exact absurd h4 (fun hc => failOk hc)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h4
  -- `Quot`
  obtain ⟨qn, s₃, h5, h6⟩ := bindOk h4
  have c2 := (p1.trans p2).toCore hok
  obtain ⟨hs3, hqn⟩ := pinAt_run (x := ConLeche.quotName) c2.ok.pins rfl h5
  rw [hs3] at h6
  have hx02 := p1.ext.trans p2.ext
  have hnq := beq_handle_eq (p1.trans p2).ok.wf (denoteN_ext hn hx02) hqn
  by_cases hq : (n == qn) = true
  · rw [if_pos hq] at h6; exact absurd h6 (fun hc => failOk hc)
  rw [if_neg hq] at h6
  -- the parameters
  obtain ⟨pc, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨p4, hpc⟩ := paramsLocal_spec (ctx.hiAt prog.length) _ _ s₂ s₄ pc (p1.trans p2).ok
    (denoteEList_take' qP.1 (denoteEList_ext p2.ext _ _ hargs1)) h7
  simp only [RV, hhp] at hpc
  subst hpc
  by_cases hpc' : (!(List.take qP.1 argsP).all fun x =>
      x.bvarB == 0 && decide (x.fvarB ≤ ctxP.hiAt progP.length)) = true
  · rw [if_pos hpc'] at h8; exact absurd h8 (fun hc => failOk hc)
  rw [if_neg hpc'] at h8
  have hpcT : ((List.take qP.1 argsP).all fun x =>
      x.bvarB == 0 && decide (x.fvarB ≤ ctxP.hiAt progP.length)) = true := by
    simpa using hpc'
  -- the former
  have c4 := (p1.trans (p2.trans p4)).toCore hok
  have hx04 := hx02.trans p4.ext
  obtain ⟨ni, s₅, h9, h10⟩ := bindOk h8
  obtain ⟨c5, niP, ⟨hni1, hni2, hni3⟩, hFni⟩ := nestInstType_spec hc ctx _
    ⟨n, us, args.take qP.1⟩ ⟨nP, usP, argsP.take qP.1⟩ s₄ s₅ ni c4.ok
    ⟨dCtx_ext _ hx04 _ _ hctx, by simp [dKey, denoteN_ext hn hx04, denoteLs_ext hus hx04,
      denoteEList_take' qP.1 (denoteEList_ext hx04 _ _ hargs')]⟩ h9
  obtain ⟨nI, cty⟩ := ni
  dsimp only at h10 hni1 hni2
  subst hni1
  by_cases hlen : (args.length != qP.1 + niP.1) = true
  · rw [if_pos hlen] at h10; exact absurd h10 (fun hc => failOk hc)
  rw [if_neg hlen] at h10
  -- the instantiation
  have hdsT : ∀ d ∈ List.take qP.1 argsP, Expr.WScoped (ctxP.hiAt progP.length) d := by
    intro d hd
    have h1 := List.all_eq_true.mp hpcT d hd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    exact ConLeche.WScoped.of_fvarsBelow (hargs d (List.mem_of_mem_take hd))
      (Expr.fvarB_le h1.2)
  have hx05 := hx04.trans c5.ext
  obtain ⟨c6, v, hv, hFv⟩ := nestContKey_spec hk henv hc ih prog progP kb n nP us usP _ _
    qP.1 cty niP.2 ns nsP hdsT hni3 s₅ s' r c5.ok
    ⟨dCtx_ext _ hx05 _ _ hctx, dProg_ext hx05 _ _ hprog, denoteN_ext hn hx05,
      denoteLs_ext hus hx05, denoteEList_take' qP.1 (denoteEList_ext hx05 _ _ hargs'),
      hni2, dState_ext hx05 _ _ hns⟩ h10
  refine ⟨c4.trans (c5.trans c6), v, hv, ?_⟩
  have hc1 : (decide (argsP.length < qP.1) || !(List.drop qP.1 argsP).all fun x =>
      !Expr.nestOcc ctxP.names ctxP.nP (ctxP.hiAt progP.length) x) = false := by
    rw [← hlenA]
    simp only [hl, decide_false, Bool.false_or, Bool.not_eq_false', ← List.not_any_eq_all_not,
      Bool.not_eq_true']
    rw [← hhp, ← hcnP]
    exact hb.symm
  have hc2 : (nP == ConLeche.quotName) = false := by rw [← hnq]; simpa using hq
  have hc4 : (argsP.length == qP.1 + niP.1) = true := by
    rw [← hlenA]; simpa using hlen
  simp only [ConLeche.nestCont, hqP]
  refine FOk.bind FOk.unwrapOr ?_
  simp only [hc1, hc2, hpcT, Bool.false_eq_true, ↓reduceIte]
  rw [hhp] at hFni
  refine FOk.bind hFni ?_
  simp only [hc4, ↓reduceIte]
  exact hFv

end ContCase

section PosFn

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1442-1496 nestPos
**The positivity function, one fuel up** (con-leche's `nestPosS_sim`, its
successor case): the reduct's cases — hole-free, a `Π`, a hole application, a
container application (`nestCont_spec`) — each the same verdict. -/
theorem nestPos_succ (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP) {fuel : Nat}
    (ih : NestPosSpec μ env fe ctx ctxP fuel) : NestPosSpec μ env fe ctx ctxP (fuel + 1) := by
  intro prog progP dep kb e eP ns nsP hw s₀ s' r hok hp hrun
  obtain ⟨hctx, hprog, he, hns⟩ := hp
  obtain ⟨hcnames, hcnP, hfind, -, -, -⟩ := dCtx_fields hctx
  have hhi : ctx.hiAt prog.length = ctxP.hiAt progP.length := by
    rw [hiAt_eq hctx, dProg_length hprog]
  rw [Arena.nestPos.eq_def] at hrun
  dsimp only at hrun
  -- the reduct
  obtain ⟨w, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨c1, wP, hwd, hww, hFw⟩ := whnf_crun hk henv hok he hw h1
  have hn1 := denoteNListE_ext c1.ext _ _ hcnames
  obtain ⟨b1, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨p2, hb1⟩ := nestOcc_spec ctx.names ctxP.names ctx.nP _ w wP s₁ s₂ b1 c1.ok.state
    ⟨hn1, hwd⟩ h3
  simp only [RV, hhi, hcnP] at hb1
  subst hb1
  have c2 := c1.trans (p2.toCore c1.ok)
  have hx02 := c1.ext.trans p2.ext
  cases hA : Expr.nestOcc ctxP.names ctxP.nP (ctxP.hiAt progP.length) wP with
  | false =>
    -- hole-free
    rw [hA] at h4
    simp only [Bool.not_false, ↓reduceIte] at h4
    obtain ⟨b2, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨p3, hb2⟩ := nestOcc_spec ctx.names ctxP.names ctx.nP _ e eP s₂ s₃ b2 c2.ok.state
      ⟨denoteNListE_ext p2.ext _ _ hn1, denote_ext he hx02⟩ h5
    simp only [RV, hhi, hcnP] at hb2
    subst hb2
    have c3 := c2.trans (p3.toCore c2.ok)
    refine ⟨?_, (.ordinary, if Expr.nestOcc ctxP.names ctxP.nP (ctxP.hiAt progP.length) eP
      then wP else eP, nsP), ?_, ?_⟩
    · split at h6 <;> (obtain ⟨rfl, rfl⟩ := pureOk h6; exact c3)
    · split at h6
      · rename_i hB
        obtain ⟨rfl, rfl⟩ := pureOk h6
        exact ⟨rfl, by rw [if_pos hB]; exact denote_ext hwd (p2.ext.trans p3.ext),
          dState_ext (c1.ext.trans (p2.ext.trans p3.ext)) _ _ hns, by rw [if_pos hB]; exact hww⟩
      · rename_i hB
        obtain ⟨rfl, rfl⟩ := pureOk h6
        exact ⟨rfl, by rw [if_neg hB]; exact denote_ext he (c1.ext.trans (p2.ext.trans p3.ext)),
          dState_ext (c1.ext.trans (p2.ext.trans p3.ext)) _ _ hns, by rw [if_neg hB]; exact hw⟩
    · simp only [ConLeche.nestPos]
      refine FOk.bind hFw ?_
      simp only [hA, Bool.not_false, ↓reduceIte]
      exact FOk.pure _
  | true =>
  rw [hA] at h4
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h4
  by_cases htg : (w.tag == ETag.forallE) = true
  · -- a `Π`
    rw [if_pos htg] at h4
    obtain ⟨o, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨hs3, ho⟩ := viewBind_run h5
    rw [hs3] at h6
    cases o with
    | none => exact absurd h6 (fun hc => failDanglingE_ok hc)
    | some q =>
    obtain ⟨a, b, bm⟩ := q
    have hwv := view_of_viewBind_tag_forallE htg ho.symm
    obtain ⟨aP, bP, rfl, ha, hb⟩ :=
      denote_forallE_inv c2.ok.state.wf hwv (denote_ext hwd p2.ext)
    simp only [Expr.WScoped] at hww
    dsimp only at h6
    obtain ⟨b3, s₄, h7, h8⟩ := bindOk h6
    obtain ⟨p4, hb3⟩ := nestOcc_spec ctx.names ctxP.names ctx.nP _ a aP s₂ s₄ b3 c2.ok.state
      ⟨denoteNListE_ext p2.ext _ _ hn1, ha⟩ h7
    simp only [RV, hhi, hcnP] at hb3
    subst hb3
    cases hB : Expr.nestOcc ctxP.names ctxP.nP (ctxP.hiAt progP.length) aP with
    | true => rw [hB] at h8; simp only [↓reduceIte] at h8; exact absurd h8 (fun hc => failOk hc)
    | false =>
    rw [hB] at h8
    simp only [Bool.false_eq_true, ↓reduceIte] at h8
    obtain ⟨fv, s₅, h9, h10⟩ := bindOk h8
    obtain ⟨p5, hfv⟩ := internFVarE_run p4.ok (denote_ext ha p4.ext) h9
    obtain ⟨b2, s₆, h11, h12⟩ := bindOk h10
    have hb5 : denoteE s₅.store b = some bP := denote_ext hb (p4.ext.trans p5.ext)
    obtain ⟨q1, q2, q3, q4, q5, -, q7⟩ := ExprOps.instantiate1Fast_run p5.ok hfv
      (by rw [hb5]; rfl) h11
    have p6 : PStep s₅ s₆ := PStep.of_caches q1 q2 q3 q4 q5
    have hb6 : denoteE s₆.store b2 = some (bP.instantiate1 (.fvar dep aP) 0) := q7 _ hb5
    have c6 := c2.trans ((p4.trans (p5.trans p6)).toCore c2.ok)
    have hx26 := p4.ext.trans (p5.ext.trans p6.ext)
    obtain ⟨q, s₇, h13, h14⟩ := bindOk h12
    obtain ⟨c7, v1, ⟨hk1, hnb, hns1, hwb⟩, hF1⟩ := ih prog progP (dep + 1) (kb + 1) b2 _ ns nsP
      (Expr.WScoped.instantiate1 hww.1 0 hww.2) s₆ s₇ q c6.ok
      ⟨dCtx_ext _ (hx02.trans hx26) _ _ hctx, dProg_ext (hx02.trans hx26) _ _ hprog, hb6,
        dState_ext (hx02.trans hx26) _ _ hns⟩ h13
    obtain ⟨k, nb, ns2⟩ := q
    dsimp only at h14 hk1 hnb hns1
    obtain ⟨nb2, s₈, h15, h16⟩ := bindOk h14
    obtain ⟨r1, r2, r3, r4, r5, -, r7⟩ := AM.of_run (P := fun t => t = s₇) rfl h15
      (ExprOps.abstract1Fast_spec fvarBSpec Arena.coreWalkFuel s₇ nb dep 0 c7.ok.state
        (by rw [hnb]; rfl))
    have p8 : PStep s₇ s₈ := PStep.of_caches r1 r2 r3 r4 r5
    obtain ⟨rr, s₉, h17, h18⟩ := bindOk h16
    obtain ⟨p9, hrr⟩ := internForallEE_run p8.ok
      (denote_ext ha (hx26.trans (c7.ext.trans p8.ext))) (r7 _ hnb) h17
    obtain ⟨rfl, rfl⟩ := pureOk h18
    refine ⟨c6.trans (c7.trans ((p8.trans p9).toCore c7.ok)),
      (v1.1, .forallE aP (v1.2.1.abstract1 dep) bm, v1.2.2),
      ⟨hk1, hrr, dState_ext (p8.ext.trans p9.ext) _ _ hns1, ?_⟩, ?_⟩
    · simp only [Expr.WScoped]
      exact ⟨hww.1, WScoped.abstract1 0 hwb⟩
    · simp only [ConLeche.nestPos]
      refine FOk.bind hFw ?_
      simp only [hA, hB, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact FOk.bind hF1 (FOk.pure _)
  · -- a head
    rw [if_neg htg] at h4
    have hnf : ∀ a b m, wP ≠ .forallE a b m := by
      intro a b m hwe
      rw [hwe] at hwd
      exact htg (by rw [tag_forallE_of_denote c1.ok.state.wf hwd]; rfl)
    have hwd2 := denote_ext hwd p2.ext
    obtain ⟨args, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨hs3, hargs⟩ := getAppArgs_run c2.ok.state hwd2 h5
    rw [hs3] at h6
    obtain ⟨hd, s₄, h7, h8⟩ := bindOk h6
    obtain ⟨hs4, hhd⟩ := getAppFn_run c2.ok.state hwd2 h7
    rw [hs4] at h8
    obtain ⟨vw, s₅, h9, h10⟩ := bindOk h8
    obtain ⟨hs5, hvw⟩ := view_run h9
    rw [hs5] at h10
    have hn2 := denoteNListE_ext p2.ext _ _ hn1
    cases vw
    case fvar i ty =>
      obtain ⟨tP, hg, -⟩ := denote_fvar_inv c2.ok.state.wf hvw hhd
      dsimp only at h10
      have hrel := nestHoleAt_rel (dCtx_ext _ hx02 _ _ hctx) (dProg_ext hx02 _ _ hprog) i
      cases hh : Arena.nestHoleAt ctx prog i with
      | none => rw [hh] at h10; exact absurd h10 (fun hc => failOk hc)
      | some h =>
      rw [hh] at h10 hrel
      obtain ⟨hP, hhP, hdh⟩ := hrel
      dsimp only at h10
      obtain ⟨bA, s₆, h11, h12⟩ := bindOk h10
      obtain ⟨p6, hbA⟩ := anyM_E_pstep (fun st => Frontend.denoteNList st.ns ctx.names =
          some ctxP.names)
        (fun hx h => denoteNListE_ext hx _ _ h)
        (fun e eP s₀ s' b hok' hq hd hrun' =>
          nestOcc_spec ctx.names ctxP.names ctx.nP _ e eP s₀ s' b hok' ⟨hq, hd⟩ hrun')
        args _ s₂ s₆ bA c2.ok.state hn2 hargs h11
      rw [hhi, hcnP] at hbA
      subst hbA
      cases hB : wP.getAppArgs.any fun x =>
          Expr.nestOcc ctxP.names ctxP.nP (ctxP.hiAt progP.length) x with
      | true => rw [hB] at h12; simp only [↓reduceIte] at h12; exact absurd h12 (fun hc => failOk hc)
      | false =>
      rw [hB] at h12
      simp only [Bool.false_eq_true, ↓reduceIte] at h12
      obtain ⟨ar, s₇, h13, h14⟩ := bindOk h12
      simp only [dHole, Option.map_eq_some_iff] at hdh
      obtain ⟨kP, hkP, rfl⟩ := hdh
      obtain ⟨hkc, -, hkd⟩ := dKey_inv hkP
      obtain ⟨p7, har⟩ := nestArity_spec ctxP hfind h.key.cname kP.cname s₆ s₇ ar p6.ok
        ⟨c2.ok.ienv.toS.mono p6.ext, denoteN_ext hkc p6.ext⟩ h13
      simp only [RV] at har
      subst har
      have hlen1 := PW.denoteEList_length hargs
      have hlen2 := PW.denoteEList_length hkd
      rw [hlen1, hlen2] at h14
      by_cases hL : (wP.getAppArgs.length + kP.ds.length ==
          ConLeche.nestArity ctxP kP.cname) = true
      · rw [if_pos hL] at h14
        obtain ⟨rfl, rfl⟩ := pureOk h14
        have c7 := c2.trans ((p6.trans p7).toCore c2.ok)
        refine ⟨c7, (if i < ctxP.hiAt 0 then
            (if (kb == 0) = true then .recursive (i - ctxP.nP) else .reflexive (i - ctxP.nP))
          else .inProgress, wP, nsP),
          ⟨?_, denote_ext hwd (p2.ext.trans (p6.ext.trans p7.ext)),
            dState_ext (hx02.trans (p6.ext.trans p7.ext)) _ _ hns, hww⟩, ?_⟩
        · simp only [hiAt_eq hctx 0, hcnP]
          by_cases hi1 : i < ctxP.hiAt 0 <;> by_cases hkb : (kb == 0) = true <;>
            simp only [hi1, hkb, if_true, if_false] <;> rfl
        · simp only [ConLeche.nestPos]
          refine FOk.bind hFw ?_
          simp only [hA, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases wP with
          | forallE a b bm => exact absurd rfl (hnf a b bm)
          | _ =>
            simp only [hg, hhP, ← List.not_any_eq_all_not, hB, Bool.not_false, Bool.true_and,
              hL, ↓reduceIte]
            exact FOk.pure _
      · rw [if_neg hL] at h14; exact absurd h14 (fun hc => failOk hc)
    case const n us =>
      obtain ⟨nm, ls, hg, hn, hls⟩ := denote_const_inv c2.ok.state.wf hvw hhd
      dsimp only at h10
      have hcont := contains_handle_eq c2.ok.state.wf hn hn2
      by_cases hC : ctx.names.contains n = true
      · rw [if_pos hC] at h10; exact absurd h10 (fun hc => failOk hc)
      rw [if_neg hC] at h10
      have hC' : ctxP.names.contains nm = false := by rw [← hcont]; simpa using hC
      obtain ⟨q, s₆, h11, h12⟩ := bindOk h10
      obtain ⟨c6, v1, ⟨hk1, hns1⟩, hF1⟩ := nestCont_spec hk henv hc ih prog progP kb n nm us ls
        args wP.getAppArgs ns nsP (Expr.WScoped.getAppArgs hww) s₂ s₆ q c2.ok
        ⟨dCtx_ext _ hx02 _ _ hctx, dProg_ext hx02 _ _ hprog, hn, hls, hargs,
          dState_ext hx02 _ _ hns⟩ h11
      obtain ⟨k, ns2⟩ := q
      dsimp only at h12 hk1 hns1
      obtain ⟨rfl, rfl⟩ := pureOk h12
      refine ⟨c2.trans c6, (v1.1, wP, v1.2),
        ⟨hk1, denote_ext hwd (p2.ext.trans c6.ext), hns1, hww⟩, ?_⟩
      simp only [ConLeche.nestPos]
      refine FOk.bind hFw ?_
      simp only [hA, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases wP with
      | forallE a b bm => exact absurd rfl (hnf a b bm)
      | _ =>
        simp only [hg, hC', Bool.false_eq_true, ↓reduceIte]
        exact FOk.bind hF1 (FOk.pure _)
    all_goals exact absurd h10 (fun hc => failOk hc)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1442-1496 nestPos
**THE POSITIVITY FUNCTION** (con-leche's `nestPosS_sim`): at every fuel, an
accepting twin run at a well-scoped input denotes a run of con-leche's
`nestPos` at `fueledOpsM μ` — the kind read, the walked form (well scoped at
the walk's depth) and the state. -/
theorem nestPos_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP) :
    ∀ fuel, NestPosSpec μ env fe ctx ctxP fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro prog progP dep kb e eP ns nsP hw s₀ s' r hok hp hrun
    rw [Arena.nestPos.eq_def] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih => exact nestPos_succ hk henv hc ih

end PosFn

/-! ## The member holes, the root crest, uniform occurrences -/

section Root

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1498-1507 nestHoles
(the cited `mapM`, one index) — member `mm`'s hole. -/
def holeAtP (ctxP : ConLeche.NestCtx) (mm : Nat) : Option Expr :=
  match ctxP.find? (ctxP.names.getD mm .anonymous) with
  | some (.indInfo cv _) => (ConLeche.instPisWith ctxP.params cv.type).map (.fvar (ctxP.nP + mm) ·)
  | _ => none

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1498-1507 nestHoles
— the twin's accumulator loop from member `mm` on: the accumulator, then
con-leche's `mapM` over the remaining indices. -/
theorem nestHolesGo_spec (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) :
    ∀ (ns : List NIdx) (nsP : List ConLeche.Name) (mm : Nat) (out : List EIdx)
      (outP : List Expr),
      ctxP.names.drop mm = nsP →
      PSpec (fun st => IFEnvOKS env fe st ∧ dCtx st env.find? ctx = some ctxP ∧
          Frontend.denoteNList st.ns ns = some nsP ∧ Frontend.denoteEList st out = some outP)
        (Arena.nestHoles.go fe ctx mm ns out)
        (ROp REL (((List.range' mm nsP.length).mapM (holeAtP ctxP)).map (outP ++ ·))) := by
  intro ns
  induction ns with
  | nil =>
    intro nsP mm out outP hdrop s₀ s' r hok hp hrun
    obtain ⟨-, -, hns, hout⟩ := hp
    simp only [Frontend.denoteNList, Option.some.injEq] at hns
    subst hns
    simp only [Arena.nestHoles.go] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, _, by simp, hout⟩
  | cons n ns ih =>
    intro nsP mm out outP hdrop s₀ s' r hok hp hrun
    obtain ⟨hie, hctx, hns, hout⟩ := hp
    obtain ⟨-, hcnP, hfind, hpar, -, -⟩ := dCtx_fields hctx
    simp only [Frontend.denoteNList] at hns
    cases hn : denoteN s₀.store.ns n with
    | none => rw [hn] at hns; simp at hns
    | some x =>
    cases hns' : Frontend.denoteNList s₀.store.ns ns with
    | none => rw [hn, hns'] at hns; simp at hns
    | some xs =>
    rw [hn, hns'] at hns
    obtain rfl := (Option.some.inj hns).symm
    have hget : ctxP.names.getD mm .anonymous = x := by
      have : (ctxP.names.drop mm)[0]? = some x := by rw [hdrop]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at this
      rw [List.getD_eq_getElem?_getD, this]; rfl
    have hdrop' : ctxP.names.drop (mm + 1) = xs := by
      rw [← List.drop_drop, hdrop]; rfl
    have hhole : holeAtP ctxP mm = _ := rfl
    simp only [List.length_cons, List.range'_succ, List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def]
    have hie' := hie s₀ rfl
    simp only [Arena.nestHoles.go] at hrun
    cases hf : fe.find? n with
    | none =>
      rw [hf] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show _ = none
      simp only [holeAtP, hget, hfind, hie'.miss hok hn hf]
      rfl
    | some ci =>
    rw [hf] at hrun
    obtain ⟨c, hc, he⟩ := find_some_rel hie' hn hf
    cases ci with
    | indInfo cv caps =>
      obtain ⟨cvP, capsP, hcv, -, rfl⟩ := denoteCI_indInfo_inv hc
      obtain ⟨-, -, hty⟩ := denoteCV_inv hcv
      dsimp only at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨p1, ho⟩ := instPisWith_spec ctx.params ctxP.params cv.type cvP.type s₀ s₁ o hok
        ⟨hpar, hty⟩ h1
      have hG : holeAtP ctxP mm =
          (ConLeche.instPisWith ctxP.params cvP.type).map (.fvar (ctxP.nP + mm) ·) := by
        simp only [holeAtP, hget, hfind, he]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk h2
        refine ⟨p1, ?_⟩
        show _ = none
        simp only [ROp] at ho
        rw [hG, ho]; rfl
      | some t =>
        obtain ⟨tP, htP, ht⟩ := ho
        dsimp only at h2
        obtain ⟨v, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨p2, hv⟩ := internFVarE_run p1.ok ht h3
        rw [hcnP] at hv
        obtain ⟨p3, hr⟩ := ih xs (mm + 1) (out ++ [v]) (outP ++ [.fvar (ctxP.nP + mm) tP]) hdrop'
          s₂ s' r p2.ok ⟨hie.mono (p1.ext.trans p2.ext), dCtx_ext _ (p1.ext.trans p2.ext) _ _ hctx,
            denoteNListE_ext (p1.ext.trans p2.ext) _ _ hns',
            denoteEList_append (denoteEList_ext (p1.ext.trans p2.ext) _ _ hout)
              (by simp [Frontend.denoteEList, hv])⟩ h4
        refine ⟨p1.trans (p2.trans p3), ?_⟩
        rw [hG, htP]
        simp only [Option.map_some, Option.bind_some]
        cases hm : (List.range' (mm + 1) xs.length).mapM (holeAtP ctxP) with
        | none => rw [hm] at hr; exact hr
        | some l =>
          rw [hm] at hr
          cases r with
          | none => simp [ROp] at hr
          | some a =>
            obtain ⟨b, hb, hbr⟩ := hr
            simp only [Option.map_some, Option.some.injEq] at hb
            subst hb
            exact ⟨_, rfl, by simpa using hbr⟩
    | _ =>
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show _ = none
      have := denoteCI_not_ind hc (by intro v caps h; exact nomatch h)
      have hG : holeAtP ctxP mm = none := by
        simp only [holeAtP, hget, hfind, he]
        cases c with
        | indInfo v k => exact absurd rfl (this v k)
        | _ => rfl
      rw [hG]; rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1498-1507 nestHoles
The member holes, exactly con-leche's (`none` included). -/
theorem nestHoles_spec (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) :
    PSpec (fun st => IFEnvOKS env fe st ∧ dCtx st env.find? ctx = some ctxP)
      (Arena.nestHoles fe ctx) (ROp REL (ConLeche.nestHoles ctxP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hie, hctx⟩ := hp
  obtain ⟨hcn, -, -, -, -, -⟩ := dCtx_fields hctx
  simp only [Arena.nestHoles] at hrun
  obtain ⟨p, hr⟩ := nestHolesGo_spec ctx ctxP ctx.names ctxP.names 0 [] [] rfl s₀ s' r hok
    ⟨hie, hctx, hcn, rfl⟩ hrun
  refine ⟨p, ?_⟩
  have e1 : ConLeche.nestHoles ctxP = (List.range' 0 ctxP.names.length).mapM (holeAtP ctxP) := by
    rw [ConLeche.nestHoles, ← List.range_eq_range']
    rfl
  rw [e1]
  cases hm : (List.range' 0 ctxP.names.length).mapM (holeAtP ctxP) with
  | none => rw [hm] at hr; exact hr
  | some l => rw [hm] at hr; simpa using hr

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1509-1515 nestRootCanon
The root frame's canonical crest of a member constructor, exactly
con-leche's. -/
theorem nestRootCanon_spec (fnd : ConLeche.Name → Option ConstantInfo)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) (cv : IConstantVal) (cvP : ConstantVal) :
    CSpec μ env fe (fun st => dCtx st fnd ctx = some ctxP ∧ Frontend.denoteCV st cv = some cvP)
      (Arena.nestRootCanon ctx cv) (ROp RE (ConLeche.nestRootCanon ctxP cvP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hctx, hcv⟩ := hp
  obtain ⟨hcn, -, -, -, hlv, -⟩ := dCtx_fields hctx
  obtain ⟨-, hlps, hty⟩ := denoteCV_inv hcv
  simp only [Arena.nestRootCanon] at hrun
  obtain ⟨t, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨c1, ht⟩ := instLPFast_cstep hok hlps hlv hty h1
  obtain ⟨p2, hr⟩ := nestCanonCrest_spec ctx.names ctxP.names ctx.lvls _ ctx.nP t _ s₁ s' r
    c1.ok.state c1.ok.pins ⟨denoteNListE_ext c1.ext _ _ hcn, denoteLs_ext hlv c1.ext, ht⟩ h2
  obtain ⟨-, hnP, -, -, -, -⟩ := dCtx_fields hctx
  rw [hnP] at hr
  exact ⟨c1.trans (p2.toCore c1.ok), hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1550-1559 nestUniformOk
Official's `check_uniform_ind_occs` at one constructor: exactly con-leche's
verdict. -/
theorem nestUniformOk_spec (fnd : ConLeche.Name → Option ConstantInfo)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) (cv : IConstantVal) (cvP : ConstantVal) :
    CSpec μ env fe (fun st => dCtx st fnd ctx = some ctxP ∧ Frontend.denoteCV st cv = some cvP)
      (Arena.nestUniformOk ctx cv) (RV (ConLeche.nestUniformOk ctxP cvP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hctx, hcv⟩ := hp
  obtain ⟨hcn, hnP, -, -, -, -⟩ := dCtx_fields hctx
  obtain ⟨-, -, hty⟩ := denoteCV_inv hcv
  simp only [Arena.nestUniformOk] at hrun
  obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hb⟩ := piDomsOcc_spec ctx.names ctxP.names ctx.nP (ctx.hiAt 0) ctx.nP cv.type
    cvP.type s₀ s₁ b hok.state ⟨hcn, hty⟩ h1
  simp only [RV, hnP, hiAt_eq hctx] at hb
  subst hb
  simp only [RV, ConLeche.nestUniformOk]
  cases hB : Expr.piDomsOcc ctxP.names ctxP.nP (ctxP.hiAt 0) ctxP.nP cvP.type with
  | true =>
    rw [hB] at h2
    simp only [↓reduceIte] at h2
    obtain ⟨rfl, rfl⟩ := pureOk h2
    exact ⟨p1.toCore hok, by simp⟩
  | false =>
  rw [hB] at h2
  simp only [Bool.false_eq_true, ↓reduceIte] at h2
  have c1 := p1.toCore hok
  obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨c2, ho⟩ := nestRootCanon_spec fnd ctx ctxP cv cvP s₁ s₂ o c1.ok
    ⟨dCtx_ext _ p1.ext _ _ hctx, denoteCV_ext hcv p1.ext⟩ h3
  simp only [Bool.not_false, Bool.true_and]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h4
    simp only [ROp] at ho
    rw [ho]
    exact ⟨c1.trans c2, rfl⟩
  | some crest =>
    obtain ⟨crestP, hcr, hc⟩ := ho
    rw [hcr]
    dsimp only at h4
    obtain ⟨occ, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨p3, hocc⟩ := nestOcc_spec ctx.names ctxP.names 0 0 crest crestP s₂ s₃ occ
      c2.ok.state ⟨denoteNListE_ext (p1.ext.trans c2.ext) _ _ hcn, hc⟩ h5
    obtain ⟨rfl, rfl⟩ := pureOk h6
    simp only [RV] at hocc
    exact ⟨c1.trans (c2.trans (p3.toCore c2.ok)), by rw [hocc]⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1561-1569 nestUniform
— one member's constructors all pass. -/
theorem nestUniformAll_spec (fnd : ConLeche.Name → Option ConstantInfo)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)),
      CSpec μ env fe (fun st => dCtx st fnd ctx = some ctxP ∧ dCtors st cs = some csP)
        (cs.allM fun c => Arena.nestUniformOk ctx c.1)
        (RV (csP.all fun c => ConLeche.nestUniformOk ctxP c.1)) := by
  intro cs
  induction cs with
  | nil =>
    intro csP s₀ s' r hok hp hrun
    obtain ⟨-, hcs⟩ := hp
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
    subst hcs
    simp only [List.allM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, rfl⟩
  | cons c cs ih =>
    intro csP s₀ s' r hok hp hrun
    obtain ⟨hctx, hcs⟩ := hp
    simp only [dCtors, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hcs
    cases hc1 : dCtor s₀.store c with
    | none => rw [hc1] at hcs; simp at hcs
    | some cP =>
    cases hcs1 : cs.mapM (dCtor s₀.store) with
    | none => rw [hc1, hcs1] at hcs; simp at hcs
    | some csP' =>
    rw [hc1, hcs1] at hcs
    simp only [Option.bind_some, Option.some.injEq] at hcs
    subst hcs
    simp only [dCtor, Option.map_eq_some_iff] at hc1
    obtain ⟨cvP, hcvP, rfl⟩ := hc1
    simp only [List.allM] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨c1, hb⟩ := nestUniformOk_spec fnd ctx ctxP c.1 cvP s₀ s₁ b hok ⟨hctx, hcvP⟩ h1
    simp only [RV] at hb
    subst hb
    cases hB : ConLeche.nestUniformOk ctxP cvP with
    | false =>
      rw [hB] at h2
      obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨c1, by simp [hB]⟩
    | true =>
      rw [hB] at h2
      obtain ⟨c2, hr⟩ := ih csP' s₁ s' r c1.ok
        ⟨dCtx_ext _ c1.ext _ _ hctx, dCtors_ext c1.ext _ _ hcs1⟩ h2
      exact ⟨c1.trans c2, by simp only [RV] at hr; simp [hB, hr]⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1561-1569 nestUniform
Official's uniform-occurrence check at every member's constructors: an
accepting twin run is an accepting con-leche run. -/
theorem nestUniform_spec (fnd : ConLeche.Name → Option ConstantInfo)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) :
    ∀ (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat))),
      CSpecF μ env fe (fun st => dCtx st fnd ctx = some ctxP ∧ css.mapM (dCtors st) = some cssP)
        (Arena.nestUniform ctx css) (fun _ _ _ => True)
        (ConLeche.nestUniform (m := FueledM) ctxP cssP) := by
  have hall : ∀ (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat))),
      CSpec μ env fe (fun st => dCtx st fnd ctx = some ctxP ∧ css.mapM (dCtors st) = some cssP)
        (Arena.nestUniform ctx css)
        (fun _ _ => ∀ cs ∈ cssP, ∀ c ∈ cs, ConLeche.nestUniformOk ctxP c.1 = true) := by
    intro css
    induction css with
    | nil =>
      intro cssP s₀ s' r hok hp hrun
      obtain ⟨-, hcs⟩ := hp
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
      subst hcs
      simp only [Arena.nestUniform] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, fun _ h => nomatch h⟩
    | cons cs css ih =>
      intro cssP s₀ s' r hok hp hrun
      obtain ⟨hctx, hcs⟩ := hp
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hcs
      cases hc1 : dCtors s₀.store cs with
      | none => rw [hc1] at hcs; simp at hcs
      | some csP =>
      cases hcs1 : css.mapM (dCtors s₀.store) with
      | none => rw [hc1, hcs1] at hcs; simp at hcs
      | some cssP' =>
      rw [hc1, hcs1] at hcs
      simp only [Option.bind_some, Option.some.injEq] at hcs
      subst hcs
      simp only [Arena.nestUniform] at hrun
      obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨c1, hb⟩ := nestUniformAll_spec fnd ctx ctxP cs csP s₀ s₁ b hok ⟨hctx, hc1⟩ h1
      simp only [RV] at hb
      subst hb
      by_cases hB : (csP.all fun c => ConLeche.nestUniformOk ctxP c.1) = true
      · rw [if_pos hB] at h2
        obtain ⟨c2, hr⟩ := ih cssP' s₁ s' r c1.ok
          ⟨dCtx_ext _ c1.ext _ _ hctx, dCtors_ext.list c1.ext _ _ hcs1⟩ h2
        refine ⟨c1.trans c2, fun cs' hcs' c hc => ?_⟩
        rcases List.mem_cons.mp hcs' with rfl | hcs'
        · exact List.all_eq_true.mp hB c hc
        · exact hr cs' hcs' c hc
      · rw [if_neg hB] at h2; exact absurd h2 (fun hc => failOk hc)
  intro css cssP s₀ s' r hok hp hrun
  obtain ⟨c, hr⟩ := hall css cssP s₀ s' r hok hp hrun
  refine ⟨c, (), trivial, ?_⟩
  have hn : cssP.findSome? (·.find? (!ConLeche.nestUniformOk ctxP ·.1)) = none := by
    rw [List.findSome?_eq_none_iff]
    intro cs hcs
    rw [List.find?_eq_none]
    intro c hc
    simp [hr cs hcs c hc]
  simp only [ConLeche.nestUniform, hn]
  exact FOk.pure ()

end Root

/-! ## The root frame and the seeds -/

section Top

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-- con-leche: none — every member's outputs, denoted. -/
def dOutss (st : EStore) (oss : List (List (List Arena.NestFieldKind × EIdx))) :
    Option (List (List (List ConLeche.NestFieldKind × Expr))) :=
  oss.mapM fun os => os.mapM (dOut st)

theorem dOutss_ext : DExt dOutss := by
  intro st st' hx xs ys h
  have h1 : DExt (fun st (os : List (List Arena.NestFieldKind × EIdx)) => os.mapM (dOut st)) :=
    dOut_ext.list
  exact mapM_option_ext (fun a b hab => h1 hx a b hab) xs ys h

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1585-1600 nestRoot
**The root frame** (con-leche's `nestRootS_sim`): every member's constructors
through `nestCtors_spec` at the root key, each at the input-derived fuel of its
crest (`nestPos_spec` at every fuel); the accumulator is the prefix of
con-leche's answer, every walked form well scoped at `hiAt 0`. -/
theorem nestRoot_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP)
    (holes : List EIdx) (holesP : List Expr)
    (hholes : ∀ x ∈ holesP, Expr.WScoped (ctxP.hiAt 0) x)
    (hlen : ctxP.names.length ≤ holesP.length)
    (hpar : ∀ x ∈ ctxP.params, Expr.WScoped (ctxP.hiAt 0) x) :
    ∀ (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat)))
      (ns : Arena.NestState) (nsP : ConLeche.NestState)
      (outs : List (List (List Arena.NestFieldKind × EIdx)))
      (outsP : List (List (List ConLeche.NestFieldKind × Expr))),
      (∀ cs ∈ cssP, ∀ c ∈ cs, c.1.type.hasFvar = false) →
      CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
          Frontend.denoteEList st holes = some holesP ∧ css.mapM (dCtors st) = some cssP ∧
          dState st ns = some nsP ∧ dOutss st outs = some outsP)
        (Arena.nestRoot μ fe ctx holes css ns outs)
        (fun st r v => dOutss st r.1 = some (outsP ++ v.1) ∧ dState st r.2 = some v.2 ∧
          ∀ os ∈ v.1, ∀ o ∈ os, Expr.WScoped (ctxP.hiAt 0) o.2)
        (ConLeche.nestRoot (fueledOpsM μ) env ctxP holesP cssP nsP) := by
  intro css
  induction css with
  | nil =>
    intro cssP ns nsP outs outsP hcl s₀ s' r hok hp hrun
    obtain ⟨-, -, hcs, hns, houts⟩ := hp
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.nestRoot] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨CoreStep.refl hok, ([], nsP), ⟨by simpa using houts, hns, fun _ h => nomatch h⟩, ?_⟩
    simp only [ConLeche.nestRoot]
    exact FOk.pure _
  | cons cs css ih =>
    intro cssP ns nsP outs outsP hcl s₀ s' r hok hp hrun
    obtain ⟨hctx, hholes', hcs, hns, houts⟩ := hp
    obtain ⟨hcn, -, -, hpar', hlv, -⟩ := dCtx_fields hctx
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hcs
    cases hc1 : dCtors s₀.store cs with
    | none => rw [hc1] at hcs; simp at hcs
    | some csP =>
    cases hcs1 : css.mapM (dCtors s₀.store) with
    | none => rw [hc1, hcs1] at hcs; simp at hcs
    | some cssP' =>
    rw [hc1, hcs1] at hcs
    simp only [Option.bind_some, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.nestRoot] at hrun
    rw [hiAt_eq hctx] at hrun
    obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨c1, v1, ⟨hv1, hns1, hw1⟩, hF1⟩ := nestCtors_spec hk henv true 0
      (fun crestP => ConLeche.nestPos (fueledOpsM μ) env ctxP (whnfWalkFuel crestP))
      (fun _ => by simp) (fun crestP => by simpa using nestPos_spec hk henv hc _)
      [] [] (ctxP.hiAt 0) ctx.lvls _ ctx.params ctxP.params ctx.names ctxP.names holes holesP
      hpar hholes hlen cs csP ns nsP [] [] (hcl csP List.mem_cons_self) s₀ s₁ q hok
      ⟨hctx, rfl, hlv, hpar', hcn, hholes', hc1, hns, rfl⟩ h1
    obtain ⟨o, ns2⟩ := q
    dsimp only at h2 hv1 hns1
    simp only [List.nil_append] at hv1
    obtain ⟨c2, v2, ⟨hv2, hns2, hw2⟩, hF2⟩ := ih cssP' ns2 v1.2 (outs ++ [o]) (outsP ++ [v1.1])
      (fun cs hcs => hcl cs (List.mem_cons_of_mem _ hcs)) s₁ s' r c1.ok
      ⟨dCtx_ext _ c1.ext _ _ hctx, denoteEList_ext c1.ext _ _ hholes',
        dCtors_ext.list c1.ext _ _ hcs1, hns1,
        mapM_option_append (dOutss_ext c1.ext _ _ houts) (by simp [hv1])⟩ h2
    refine ⟨c1.trans c2, (v1.1 :: v2.1, v2.2), ⟨by rw [hv2]; simp, hns2, fun os hos o ho => ?_⟩,
      ?_⟩
    · rcases List.mem_cons.mp hos with rfl | hos
      · exact hw1 o ho
      · exact hw2 os hos o ho
    · simp only [ConLeche.nestRoot]
      exact FOk.bind hF1 (FOk.bind hF2 (FOk.pure _))

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1630-1638 nestSeedOf
A resolved class as a seed, exactly con-leche's key. -/
theorem nestSeedOf_spec (fnd : ConLeche.Name → Option ConstantInfo) (ctx : Arena.NestCtx)
    (ctxP : ConLeche.NestCtx) (holes : List EIdx) (holesP : List Expr) (I : NIdx)
    (IP : ConLeche.Name) (us : LsIdx) (usP : List Level) (ds : List EIdx) (dsP : List Expr)
    (nPc : Nat) :
    PSpecP (fun st => dCtx st fnd ctx = some ctxP ∧ Frontend.denoteEList st holes = some holesP ∧
        denoteN st.ns I = some IP ∧ denoteLs st.lss us = some usP ∧
        Frontend.denoteEList st ds = some dsP)
      (Arena.nestSeedOf ctx holes I us ds nPc)
      (fun st r => dKey st r.1 = some (ConLeche.nestSeedOf ctxP holesP IP usP dsP nPc).1 ∧
        r.2 = nPc) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hctx, hholes, hI, hus, hds⟩ := hp
  obtain ⟨hcn, hnP, -, hpar, hlv, -⟩ := dCtx_fields hctx
  simp only [Arena.nestSeedOf] at hrun
  obtain ⟨ds2, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, hds2⟩ := mapM_RE_P (fun st => dCtx st fnd ctx = some ctxP ∧
        Frontend.denoteEList st holes = some holesP)
    (fun hx h => ⟨dCtx_ext fnd hx _ _ h.1, denoteEList_ext hx _ _ h.2⟩)
    (G := fun x => (x.replaceApps (ConLeche.nestCanonSub ctxP.names (ctxP.lps.map .param)
      ctxP.nP) 0 ctxP.nP).replaceFVars (ConLeche.nestKeyMap ctxP.params holesP))
    (fun e eP s₀ s' r hok hpins hp hrun => by
      obtain ⟨⟨hctx', hholes'⟩, he⟩ := hp
      obtain ⟨hcn', hnP', -, hpar', hlv', -⟩ := dCtx_fields hctx'
      obtain ⟨y, s₁, k1, k2⟩ := bindOk hrun
      obtain ⟨q1, hy⟩ := replaceApps_spec ctx.names ctxP.names ctx.lvls _ 0 ctx.nP e eP s₀ s₁ y
        hok hpins ⟨hcn', hlv', he⟩ k1
      rw [hnP'] at hy
      obtain ⟨q2, hr⟩ := replaceFVars_spec (.keyMap ctx.params holes)
        (ConLeche.nestKeyMap ctxP.params holesP) y _ s₁ s' r q1.ok
        (Inductives.PinsOK.ofPStep hpins q1)
        ⟨⟨ctxP.params, holesP, denoteEList_ext q1.ext _ _ hpar',
          denoteEList_ext q1.ext _ _ hholes', rfl⟩, hy⟩ k2
      exact ⟨q1.trans q2, hr⟩)
    ds dsP s₀ s₁ ds2 hok hpins ⟨⟨hctx, hholes⟩, hds⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨p1, by simp [dKey, denoteN_ext hI p1.ext, denoteLs_ext hus p1.ext, hds2,
    ConLeche.nestSeedOf], rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1640-1654 nestSeeds
(`key.ds.foldl (fun a d => max a (whnfWalkFuel d)) fuelSlack`) — the seed's
fuel, the twin's `foldlM` over its parameters. -/
theorem seedFuel_spec :
    ∀ (ds : List EIdx) (dsP : List Expr) (a : Nat),
      PSpec (fun st => Frontend.denoteEList st ds = some dsP)
        (ds.foldlM (fun a d => do
          let w ← Arena.whnfWalkFuel d
          pure (max a w)) a)
        (RV (dsP.foldl (fun a d => max a (ConLeche.whnfWalkFuel d)) a)) := by
  intro ds
  induction ds with
  | nil =>
    intro dsP a s₀ s' r hok hd hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    simp only [List.foldlM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons d ds ih =>
    intro dsP a s₀ s' r hok hd hrun
    obtain ⟨x, xs, hx, hxs, rfl⟩ := denoteEList_cons hd
    simp only [List.foldlM_cons] at hrun
    obtain ⟨a1, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨w, s₂, h3, h4⟩ := bindOk h1
    obtain ⟨p1, hw⟩ := whnfWalkFuel_spec d x s₀ s₂ w hok hx h3
    simp only [RV] at hw
    subst hw
    obtain ⟨rfl, hs⟩ := pureOk h4
    subst hs
    obtain ⟨p2, hr⟩ := ih xs _ s₁ s' r p1.ok (denoteEList_ext p1.ext _ _ hxs) h2
    exact ⟨p1.trans p2, by simpa using hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1640-1654 nestSeeds
**The seeds walked** (con-leche's `nestSeedsS_sim`): each seed a container
instance met at the empty frame stack (`nestContKey_spec`), at the fuel its
parameters give. -/
theorem nestSeeds_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (hc : NestCtxOk ctxP) :
    ∀ (ks : List (Arena.NestKey × Nat)) (ksP : List (ConLeche.NestKey × Nat))
      (ns : Arena.NestState) (nsP : ConLeche.NestState),
      (∀ k ∈ ksP, ∀ x ∈ k.1.ds, Expr.WScoped (ctxP.hiAt 0) x) →
      CSpecF μ env fe (fun st => dCtx st env.find? ctx = some ctxP ∧
          ks.mapM (fun k => (dKey st k.1).map (·, k.2)) = some ksP ∧ dState st ns = some nsP)
        (Arena.nestSeeds μ fe ctx ks ns) (fun st r v => dState st r = some v)
        (ConLeche.nestSeeds (fueledOpsM μ) env ctxP ksP nsP) := by
  intro ks
  induction ks with
  | nil =>
    intro ksP ns nsP hw s₀ s' r hok hp hrun
    obtain ⟨-, hks, hns⟩ := hp
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hks
    subst hks
    simp only [Arena.nestSeeds] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, nsP, hns, by simp only [ConLeche.nestSeeds]; exact FOk.pure _⟩
  | cons k ks ih =>
    intro ksP ns nsP hw s₀ s' r hok hp hrun
    obtain ⟨hctx, hks, hns⟩ := hp
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hks
    cases hk1 : (dKey s₀.store k.1).map (·, k.2) with
    | none => rw [hk1] at hks; simp at hks
    | some kP =>
    cases hks1 : ks.mapM (fun k => (dKey s₀.store k.1).map (·, k.2)) with
    | none => rw [hk1, hks1] at hks; simp at hks
    | some ksP' =>
    rw [hk1, hks1] at hks
    simp only [Option.bind_some, Option.some.injEq] at hks
    subst hks
    simp only [Option.map_eq_some_iff] at hk1
    obtain ⟨keyP, hkey, rfl⟩ := hk1
    obtain ⟨key, nPc⟩ := k
    dsimp only at hkey
    obtain ⟨hkc, hkl, hkd⟩ := dKey_inv hkey
    simp only [Arena.nestSeeds] at hrun
    -- the fuel
    obtain ⟨f, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, hf⟩ := seedFuel_spec key.ds keyP.ds Arena.fuelSlack s₀ s₁ f hok.state hkd h1
    simp only [RV, show Arena.fuelSlack = ConLeche.fuelSlack from rfl] at hf
    subst hf
    have c1 := p1.toCore hok
    -- the former
    obtain ⟨q, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨c2, niP, ⟨-, hni2, hni3⟩, hFni⟩ := nestInstType_spec hc ctx (ctx.hiAt 0) key keyP
      s₁ s₂ q c1.ok ⟨dCtx_ext _ p1.ext _ _ hctx, dKey_ext p1.ext _ _ hkey⟩ h3
    obtain ⟨nI, cty⟩ := q
    dsimp only at h4 hni2
    rw [hiAt_eq hctx] at hFni
    -- the instantiation, at the empty stack
    obtain ⟨q, s₃, h5, h6⟩ := bindOk h4
    have hx02 := p1.ext.trans c2.ext
    obtain ⟨c3, v1, ⟨-, hns1⟩, hF1⟩ := nestContKey_spec hk henv hc
      (nestPos_spec hk henv hc (keyP.ds.foldl (fun a d => max a (ConLeche.whnfWalkFuel d))
        ConLeche.fuelSlack))
      [] [] 0 key.cname keyP.cname key.lvls keyP.lvls key.ds keyP.ds nPc cty niP.2 ns nsP
      (hw _ List.mem_cons_self) hni3 s₂ s₃ q c2.ok
      ⟨dCtx_ext _ hx02 _ _ hctx, rfl, denoteN_ext hkc hx02, denoteLs_ext hkl hx02,
        denoteEList_ext hx02 _ _ hkd, hni2, dState_ext hx02 _ _ hns⟩ h5
    obtain ⟨kk, ns2⟩ := q
    dsimp only at h6 hns1
    obtain ⟨c4, v, hv, hF⟩ := ih ksP' ns2 v1.2
      (fun k hk => hw k (List.mem_cons_of_mem _ hk)) s₃ s' r c3.ok
      ⟨dCtx_ext _ (hx02.trans c3.ext) _ _ hctx,
        mapM_option_ext (fun a b h => by
          simp only [Option.map_eq_some_iff] at h ⊢
          obtain ⟨x, hx, rfl⟩ := h
          exact ⟨x, dKey_ext (hx02.trans c3.ext) _ _ hx, rfl⟩) _ _ hks1, hns1⟩ h6
    refine ⟨c1.trans (c2.trans (c3.trans c4)), v, hv, ?_⟩
    simp only [ConLeche.nestSeeds]
    exact FOk.bind hFni (FOk.bind hF1 hF)

end Top

end ConRon.Bridge.Inductives
