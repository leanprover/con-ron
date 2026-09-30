/-
# `ConRon.Bridge.Inductives.BlockInstall` — Theorem 1 for the uniform install's stages

`Arena/Inductives/BlockInstall.lean`'s twins against
`ConLeche/Kernel/Inductives/BlockInstall.lean` (task #105), whose `…F` index
twins (`BlockInstallF.lean`) the twin collapses (its module note, deviation 1):
the capability record, official's `is_rec`, the formers' stage (telescopes,
the two agreements, the cons), the constructors' stage, the positivity check
on the stored constructors, the index sorts and the constructors' cons.

**Grades.**  `piDomsMentionAny` and `blockRawRec` are pure (`PSpec`).
`blockCapsAt` reads the result sort back through the CACHED `readLevelM`, whose
answer is the denotation only under `ReadLCacheOK`, so it is `CSpec`, and so is
`consBlockInds`, which calls it between its pushes.  Every stage that calls
the knot is `CSpecF` against con-leche's function at `fueledOpsM μ` — the
template is upstream's cached bridge (`ConLeche/Verify/Cached/BlockRunC.lean`'s
`checkBlockTeleS_sim` … `checkBlockIdxSortsS_sim`, `NestPosC.lean`'s
`checkAbsCtorSortsS_sim`, `blockNestCtxS_sim`, `checkBlockPositivityS_sim`),
and every statement carries exactly the scoping facts those carry.
`consBlockCtors` is pure on both sides (`InstRel`).

**The formers' stage runs its knot calls at the ENTRY index** and pushes the
formers only after the last of them, so `checkBlockInds_spec` is `CSpecF` at
`env fe`: `CheckOK μ env fe` still holds at the end.  Its answer carries the
new index `fe₁` as an `InstRel` denoting `env₁`, and the index spec at `fe₁`
(`IFEnvOKS`), which is what the caller's flush needs (`ReadOK.flush`) to get
`CheckOK μ env₁ fe₁`.

**Lists of records** are denoted by `List.mapM` of the record denotation
(`Frontend.denoteCV`, `dCtors`, `denoteLLists`), as `BlockParts.lean`'s
readers state them.  The twin's two side-by-side lists (`checkBlockCtors`,
`checkBlockIdxSorts`) are con-leche's `zip`.
-/
import ConRon.Bridge.Inductives.SumInstall
import ConRon.Bridge.Inductives.BlockParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

namespace BI

/-! ## Small helpers (local; see the report for the ones that belong in a
shared file) -/

/-- con-leche: none — the two constructor-list denotations agree:
`Records.lean`'s `dCtors` (a `mapM`) is `Run.lean`'s `denoteCtors`. -/
theorem dCtors_eq_denoteCtors (st : EStore) :
    ∀ cs : List (IConstantVal × Nat), dCtors st cs = denoteCtors st cs
  | [] => rfl
  | (cv, n) :: cs => by
    have ih := dCtors_eq_denoteCtors st cs
    simp only [dCtors] at ih ⊢
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, dCtor, denoteCtors, ih]
    cases Frontend.denoteCV st cv <;> cases denoteCtors st cs <;> rfl

/-- con-leche: none — an accepting `unwrapOr` had a value and moved nothing. -/
theorem unwrapOr_ok {α : Type} {o : Option α} {e : Arena.CheckError} {a : α}
    {s s' : AState} (h : Arena.unwrapOr o e s = .ok (a, s')) : o = some a ∧ s' = s := by
  cases o with
  | none => exact absurd h (fun hc => failOk hc)
  | some x =>
    simp only [Arena.unwrapOr] at h
    obtain ⟨rfl, rfl⟩ := pureOk h
    exact ⟨rfl, rfl⟩

/-- con-leche: none — an accepting `liftFueled` had a value and moved nothing. -/
theorem liftFueled_ok {α : Type} {w : String} {o : Option α} {a : α}
    {s s' : AState} (h : Arena.liftFueled w o s = .ok (a, s')) : o = some a ∧ s' = s := by
  cases o with
  | none => exact absurd h (fun hc => failOk hc)
  | some x =>
    simp only [Arena.liftFueled] at h
    obtain ⟨rfl, rfl⟩ := pureOk h
    exact ⟨rfl, rfl⟩

theorem fok_unwrapOr {α : Type} {a : α} {e : ConLeche.CheckError} :
    FOk (ConLeche.unwrapOr (m := FueledM) (some a) e) a := FOk.pure a

theorem fok_liftFueled {α : Type} {a : α} {w : String} :
    FOk (ConLeche.liftFueled (m := FueledM) w (some a)) a := FOk.pure a

/-- con-leche: none — `lvlEq?` at the core grade: the store stands still and
the verdict is `Level.isEquiv` of the denotations (`Core.lvlEq?_spec`). -/
theorem lvlEq?_crun {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    {u v : LIdx} {uP vP : Level} {r : Option Bool} (hok : CheckOK μ env fe s)
    (hu : denoteL s.store.ls u = some uP) (hv : denoteL s.store.ls v = some vP)
    (hrun : Arena.lvlEq? u v s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧ r = Level.isEquiv uP vP := by
  obtain ⟨h1, h2, h3, lu, lv, hlu, hlv, ha⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (Core.lvlEq?_spec s u v hok)
  rw [hu] at hlu; rw [hv] at hlv
  cases hlu; cases hlv
  exact ⟨⟨h1, by rw [h2]; exact Ext.refl _, h3⟩, ha⟩

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

/-- con-leche: none — a denoted constructor list's names. -/
theorem dCtors_names {st : EStore} :
    ∀ {cs : List (IConstantVal × Nat)} {csP : List (ConstantVal × Nat)},
      dCtors st cs = some csP →
      Frontend.denoteNList st.ns (cs.map (·.1.name)) = some (csP.map (·.1.name))
  | [], csP, h => by
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | x :: xs, csP, h => by
    obtain ⟨y, ys', rfl, hy, hys⟩ := mapM_option_cons_inv h
    simp only [dCtor, Option.map_eq_some_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hz, dCtors_names hys]

end BI

open BI

/-! ## The capability record -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:49-81 blockCapsAt
**The capability record of member `mi`**, exactly.  CORE grade: the result
sort is read back through the cached `readLevelM` (`readLevelM_denote_core`),
and the default member's `etaCtor` is the zero handle, `.anonymous` under
`PinsOK.anon`. -/
theorem blockCapsAt_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (mi : Nat) (isRec : Bool) :
    CSpec μ env fe (fun st => dShape st p = some pP)
      (Arena.blockCapsAt p mi isRec)
      (fun st r => Frontend.denoteCaps st r = some (ConLeche.blockCapsAt pP mi isRec)) := by
  intro s₀ s' r hok hp hrun
  have hnames := BlockShape.memberNames_spec hp
  have hk := BlockShape.k_spec hp
  obtain ⟨ms, rs, el, sP, hms, -, -, hsP, rfl⟩ := dShape_inv hp
  have hanon := hok.pins.anon
  have hg := mapM_option_getElem?_bind hms mi
  simp only [Arena.blockCapsAt] at hrun
  simp only [ConLeche.blockCapsAt, List.getD_eq_getElem?_getD]
  cases hmi : p.members[mi]? with
  | none =>
    rw [hmi] at hrun hg
    simp only [Option.bind_none] at hg
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨CoreStep.refl hok, ?_⟩
    rw [hg]
    simp only [Option.getD_none]
    simp only [Frontend.denoteCaps, hanon, hnames]
    rfl
  | some m =>
    rw [hmi] at hrun hg
    simp only [Option.bind_some] at hg
    obtain ⟨mP, hmP⟩ : ∃ mP, dMember s₀.store m = some mP := by
      cases h : dMember s₀.store m with
      | none =>
        exfalso
        rw [h] at hg
        have h1 := List.getElem?_eq_none_iff.mp hg
        obtain ⟨h2, -⟩ := List.getElem?_eq_some_iff.mp hmi
        have hl := mapM_option_length hms
        omega
      | some mP => exact ⟨mP, rfl⟩
    rw [hmP] at hg
    rw [hg]
    simp only [Option.getD_some]
    obtain ⟨cv, cs, hcv, hcs, rfl⟩ := dMember_inv hmP
    dsimp only at hrun ⊢
    cases hc : m.ctors with
    | nil =>
      rw [hc] at hrun hcs
      simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
      subst hcs
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨CoreStep.refl hok, ?_⟩
      simp only [Frontend.denoteCaps, hanon, hnames, List.map_nil]
      rfl
    | cons c rest =>
      rw [hc] at hrun hcs
      obtain ⟨cP, restP, rfl, hcP, hrestP⟩ := mapM_option_cons_inv hcs
      obtain ⟨cvP, hcvP, rfl⟩ : ∃ cvP, Frontend.denoteCV s₀.store c.1 = some cvP ∧
          cP = (cvP, c.2) := by
        simp only [dCtor, Option.map_eq_some_iff] at hcP
        obtain ⟨x, hx, rfl⟩ := hcP
        exact ⟨x, hx, rfl⟩
      cases rest with
      | cons c' rest' =>
        obtain ⟨cP', restP', rfl, hcP', hrestP'⟩ := mapM_option_cons_inv hrestP
        obtain ⟨rfl, rfl⟩ := pureOk hrun
        refine ⟨CoreStep.refl hok, ?_⟩
        have hall := dCtors_names hcs
        simp only [Frontend.denoteCaps, hanon, hnames, hall]
      | nil =>
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrestP
        subst hrestP
        dsimp only at hrun
        obtain ⟨l, s₁, h1, h2⟩ := bindOk hrun
        have hl := readLevelM_denote_core hok (PStep.refl hok.state) h1
        rw [hsP] at hl
        obtain rfl := (Option.some.inj hl).symm
        have p1 := readLevelM_pstep hok.state h1
        obtain ⟨rfl, rfl⟩ := pureOk h2
        refine ⟨p1.toCore hok, ?_⟩
        have hx := p1.ext
        simp only [Frontend.denoteCaps,
          denoteNListE_ext hx _ _ hnames, denoteN_ext (denoteCV_name hcvP) hx,
          Frontend.denoteNList]
        simp only [Option.some.injEq, ConLeche.BlockShape.k, Arena.BlockShape.k,
          mapM_option_length hms] at hk ⊢
        generalize m.nIdx = a
        generalize c.2 = b
        generalize p.isProp = ip
        cases a <;> cases b <;> cases ip <;> cases isRec <;> rfl

/-! ## Official's `is_rec` -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:83-88 Expr.piDomsMentionAny
The syntactic telescope's domains, each through `mentionsAnyConst`.  The
twin's fuel only fails. -/
theorem piDomsMentionAny_spec (names : List NIdx) (namesP : List ConLeche.Name) :
    ∀ (fuel : Nat) (e : EIdx) (eP : Expr),
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧ denoteE st e = some eP)
      (Arena.piDomsMentionAny names fuel e) (RV (Expr.piDomsMentionAny namesP eP)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro e eP s₀ s' r hok _ hrun
    simp only [Arena.piDomsMentionAny] at hrun
    exact absurd hrun (fun h => failOk h)
  | succ n ih =>
    intro e eP s₀ s' r hok hp hrun
    obtain ⟨hT, hd⟩ := hp
    simp only [Arena.piDomsMentionAny] at hrun
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [if_pos htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨hs1, ho⟩ := PW.viewBind_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => PW.failDanglingE_ok hc)
      | some q =>
        obtain ⟨d, b, m⟩ := q
        have hw := view_of_viewBind_tag_forallE htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨c, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨p3, hc⟩ := mentionsAnyConst_spec names namesP d dP s₀ s₂ c hok ⟨hT, hdd⟩ h3
        simp only [RV] at hc
        subst hc
        by_cases hb : Expr.mentionsAnyConst namesP dP = true
        · rw [if_pos hb] at h4
          obtain ⟨rfl, rfl⟩ := pureOk h4
          exact ⟨p3, by simp [Expr.piDomsMentionAny, hb]⟩
        · rw [if_neg hb] at h4
          obtain ⟨p4, h5⟩ := ih b bP s₂ s' r p3.ok
            ⟨denoteNListE_ext p3.ext _ _ hT, denote_ext hbd p3.ext⟩ h4
          refine ⟨p3.trans p4, ?_⟩
          simp only [RV] at h5
          simp [Expr.piDomsMentionAny, hb, h5]
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show false = Expr.piDomsMentionAny namesP eP
      cases eP with
      | forallE d b m => exact absurd (PW.tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => rfl

/-- con-leche: none — `List.anyM` at the pure frame, over a denoted list, the
predicate's own precondition `Q` carried along. -/
theorem anyM_pstep {α β : Type} (d : EStore → α → Option β) (hd : DExt d)
    (Q : EStore → Prop) (hQ : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (f : α → AM Bool) (g : β → Bool)
    (hf : ∀ x y, PSpec (fun st => Q st ∧ d st x = some y) (f x) (RV (g y))) :
    ∀ (xs : List α) (ys : List β),
      PSpec (fun st => Q st ∧ xs.mapM (d st) = some ys) (xs.anyM f) (RV (ys.any g)) := by
  intro xs
  induction xs with
  | nil =>
    intro ys s₀ s' r hok hp hrun
    obtain ⟨-, hys⟩ := hp
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hys
    subst hys
    simp only [List.anyM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons x xs ih =>
    intro ys s₀ s' r hok hp hrun
    obtain ⟨hq, hys⟩ := hp
    obtain ⟨y, ys', rfl, hy, hys'⟩ := mapM_option_cons_inv hys
    simp only [List.anyM] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, hb⟩ := hf x y s₀ s₁ b hok ⟨hq, hy⟩ h1
    simp only [RV] at hb
    subst hb
    cases hg : g y with
    | true =>
      rw [hg] at h2
      obtain ⟨rfl, rfl⟩ := pureOk h2
      exact ⟨p1, by simp [hg]⟩
    | false =>
      rw [hg] at h2
      obtain ⟨p2, h3⟩ := ih ys' s₁ s' r p1.ok
        ⟨hQ p1.ext hq, hd.list p1.ext _ _ hys'⟩ h2
      exact ⟨p1.trans p2, by simp only [RV] at h3 ⊢; simp [hg, h3]⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:90-102 blockRawRec
**Official's `is_rec`**, exactly: some member occurs in some binder domain
of the syntactic telescope of some declared constructor type. -/
theorem blockRawRec_spec (p : Arena.BlockParts) (pP : ConLeche.BlockParts) :
    PSpec (fun st => dParts st p = some pP) (Arena.blockRawRec p)
      (RV (ConLeche.blockRawRec pP)) := by
  intro s₀ s' r hok hp hrun
  simp only [dParts, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hnames := BlockShape.memberNames_spec hq
  obtain ⟨ms, rs, el, sP, hms, -, -, -, rfl⟩ := dShape_inv hq
  simp only [Arena.blockRawRec] at hrun
  have hQ : ∀ {st st' : EStore}, Ext st st' →
      Frontend.denoteNList st.ns p.shape.memberNames = some (ConLeche.BlockShape.memberNames
        ⟨ms, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩) →
      Frontend.denoteNList st'.ns p.shape.memberNames = some (ConLeche.BlockShape.memberNames
        ⟨ms, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩) :=
    fun hx h => denoteNListE_ext hx _ _ h
  have hin : ∀ (c : IConstantVal × Nat) (cP : ConstantVal × Nat),
      PSpec (fun st => Frontend.denoteNList st.ns p.shape.memberNames = some
          (ConLeche.BlockShape.memberNames
            ⟨ms, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩) ∧
          dCtor st c = some cP)
        (Arena.piDomsMentionAny p.shape.memberNames coreWalkFuel c.1.type)
        (RV (cP.1.type.piDomsMentionAny (ConLeche.BlockShape.memberNames
            ⟨ms, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩))) := by
    intro c cP s₀ s' r hok hp hrun
    obtain ⟨hT, hc⟩ := hp
    simp only [dCtor, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc
    exact piDomsMentionAny_spec _ _ coreWalkFuel c.1.type cv.type s₀ s' r hok
      ⟨hT, denoteCV_type hcv⟩ hrun
  have hout : ∀ (m : Arena.MemberShape) (mP : ConLeche.MemberShape),
      PSpec (fun st => Frontend.denoteNList st.ns p.shape.memberNames = some
          (ConLeche.BlockShape.memberNames
            ⟨ms, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩) ∧
          dMember st m = some mP)
        (m.ctors.anyM fun c => Arena.piDomsMentionAny p.shape.memberNames coreWalkFuel c.1.type)
        (RV (mP.ctors.any fun c => c.1.type.piDomsMentionAny (ConLeche.BlockShape.memberNames
            ⟨ms, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩))) := by
    intro m mP s₀ s' r hok hp hrun
    obtain ⟨hT, hm⟩ := hp
    obtain ⟨cv, cs, -, hcs, rfl⟩ := dMember_inv hm
    exact anyM_pstep dCtor dCtor_ext _ hQ _ _ hin m.ctors cs s₀ s' r hok ⟨hT, hcs⟩ hrun
  exact anyM_pstep dMember dMember_ext _ hQ _ _ hout p.shape.members ms s₀ s' r hok
    ⟨hnames, hms⟩ hrun

/-! ## Stage 1: the formers -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:106-117 checkBlockTele
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:27-36 checkBlockTeleF
One member's type former, against `checkBlockTele (fueledOpsM μ)`; the
stored type is closed (`checkBlockTeleS_sim`'s answer). -/
theorem checkBlockTele_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (nP : Nat) (ms : Arena.MemberShape) (msP : ConLeche.MemberShape) :
    CSpecF μ env fe
      (fun st => dMember st ms = some msP ∧ denoteFEnv st fe = some env)
      (Arena.checkBlockTele μ fe nP ms)
      (fun st r v => Frontend.denoteCV st r.1 = some v.1 ∧ denoteL st.ls r.2 = some v.2 ∧
        Expr.WScoped 0 v.1.type)
      (ConLeche.checkBlockTele (fueledOpsM μ) env nP msP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hm, hfe⟩ := hpre
  obtain ⟨cv, cs, hcv, -, rfl⟩ := dMember_inv hm
  simp only [Arena.checkBlockTele] at hrun
  obtain ⟨cvA, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨c1, cAP, F₁, hcA, hF₁⟩ := checkConstantVal_bridge hμ hk hok henv hcv k1
  have hw1 : Expr.WScoped 0 cAP.type :=
    Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  have fk1 : FOk (ConLeche.checkConstantVal (fueledOpsM μ) env cv) cAP :=
    ⟨F₁, by rw [checkConstantVal_datF]; exact hF₁⟩
  obtain ⟨t2, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨c2, ⟨cvTaP, sP⟩, ⟨h2a, h2b, hw2⟩, fk2⟩ := checkSumTele_specF fe hμ hk henv ms.cvT cv
    (nP + ms.nIdx) cvA cAP hw1 s₁ s₂ t2 c1.ok
    ⟨denoteCV_ext hcv c1.ext, hcA, denoteFEnv_ext c1.ext hfe⟩ k2
  obtain ⟨cvTa, sI⟩ := t2
  dsimp only at h2a h2b hw2 z2
  obtain ⟨sq, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨rfl, hsq⟩ := stripPis_pstep c2.ok.state (denoteCV_type h2a) k3
  cases sq with
  | none => exact absurd z3 (fun h => failOk h)
  | some q =>
  obtain ⟨bs, body⟩ := q
  obtain ⟨xs, x, hxs, hbody⟩ := stripPis_some hsq
  dsimp only at z3
  obtain ⟨srt, s₄, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hsrt⟩ := internSortE_run c2.ok.state h2b k4
  have hbeq := beq_ehandle_eq p4.ok.wf (denote_ext hbody p4.ext) hsrt
  by_cases hb : (body == srt) = true
  · rw [if_pos hb] at z4
    obtain ⟨rfl, rfl⟩ := pureOk z4
    have c4 := c1.trans (c2.trans (p4.toCore c2.ok))
    refine ⟨c4, (cvTaP, sP), ⟨denoteCV_ext h2a p4.ext, denoteL_ext h2b p4.ext, hw2⟩, ?_⟩
    rw [hb] at hbeq
    unfold ConLeche.checkBlockTele
    refine FOk.bind fk1 (FOk.bind fk2 ?_)
    simp only [hxs]
    refine FOk.bind fok_unwrapOr ?_
    exact FOk.ite_pos (by simpa using hbeq.symm) (FOk.pure _)
  · rw [if_neg hb] at z4
    exact absurd z4 (fun h => failOk h)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:119-126 checkBlockTeles
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:38-45 checkBlockTelesF
The members' type formers, in block order; every stored type closed
(`checkBlockTelesS_sim`). -/
theorem checkBlockTeles_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (nP : Nat) :
    ∀ (mss : List Arena.MemberShape) (mssP : List ConLeche.MemberShape),
    CSpecF μ env fe
      (fun st => mss.mapM (dMember st) = some mssP ∧ denoteFEnv st fe = some env)
      (Arena.checkBlockTeles μ fe nP mss)
      (fun st r v => r.mapM (dCvL st) = some v ∧ ∀ x ∈ v, Expr.WScoped 0 x.1.type)
      (ConLeche.checkBlockTeles (fueledOpsM μ) env nP mssP) := by
  intro mss
  induction mss with
  | nil =>
    intro mssP s₀ s' r hok hpre hrun
    obtain ⟨hms, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.checkBlockTeles] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], ⟨rfl, fun _ h => nomatch h⟩, FOk.pure _⟩
  | cons ms rest ih =>
    intro mssP s₀ s' r hok hpre hrun
    obtain ⟨hms, hfe⟩ := hpre
    obtain ⟨msP, restP, rfl, hm, hrest⟩ := mapM_option_cons_inv hms
    simp only [Arena.checkBlockTeles] at hrun
    obtain ⟨t1, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, v1, ⟨h1a, h1b, hw1⟩, fk1⟩ := checkBlockTele_specF fe hμ hk henv nP ms msP
      s₀ s₁ t1 hok ⟨hm, hfe⟩ k1
    obtain ⟨t2, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨c2, v2, ⟨h2, hw2⟩, fk2⟩ := ih restP s₁ s₂ t2 c1.ok
      ⟨dMember_ext.list c1.ext _ _ hrest, denoteFEnv_ext c1.ext hfe⟩ k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
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
`checkBlockDomsAt (fueledOpsM μ)`, the scoping hypotheses split as
`checkBlockDomsAtS_sim`'s (`hc` for the opened variables' annotations, `ht`
for the expected domains). -/
theorem checkBlockDomsAt_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (off : Nat)
    (fvs doms : List EIdx) (fvsP domsP : List Expr)
    (hc : ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → Expr.WScoped (off + i) x.fvarTypeD)
    (ht : ∀ (i : Nat) (x : Expr), domsP[i]? = some x → Expr.WScoped (off + i) x) :
    ∀ (j : Nat),
    CSpecF μ env fe
      (fun st => Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st doms = some domsP)
      (Arena.checkBlockDomsAt μ fe off fvs doms j) (fun _ _ _ => True)
      (ConLeche.checkBlockDomsAt (fueledOpsM μ) env off fvsP domsP j) := by
  have hknot := hk.knot env fe henv
  intro j
  induction j with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.checkBlockDomsAt] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, (), trivial, FOk.pure ()⟩
  | succ j ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hfvs, hdoms⟩ := hpre
    simp only [Arena.checkBlockDomsAt] at hrun
    obtain ⟨a, s1, k1, hz1⟩ := bindOk hrun
    obtain ⟨ha, hs1⟩ := unwrapOr_ok k1
    subst s1
    obtain ⟨b, s2, k2, hz2⟩ := bindOk hz1
    obtain ⟨hb, hs2⟩ := unwrapOr_ok k2
    subst s2
    obtain ⟨aP, haP, hda⟩ := ExprOps.denoteEList_getElem? fvs fvsP hfvs j a ha
    obtain ⟨bP, hbP, hdb⟩ := ExprOps.denoteEList_getElem? doms domsP hdoms j b hb
    obtain ⟨t, s3, k3, hz3⟩ := bindOk hz2
    obtain ⟨hs3, ht3⟩ := fvarTypeD_run hok.state hda k3
    subst s3
    obtain ⟨c, s4, k4, hz4⟩ := bindOk hz3
    obtain ⟨hok4, hx4, hp4, hsim⟩ := AM.of_run (P := fun u => u = s₀)
      (Q := fun r u => CheckOK μ env fe u ∧ Ext s₀.store u.store ∧
        u.pins = s₀.pins ∧
        Core.SimV (ConLeche.isDefEqCore μ env) (off + j) aP.fvarTypeD bP r)
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
    refine FOk.bind fok_unwrapOr (FOk.bind fok_unwrapOr (FOk.bind fkd ?_))
    simpa using fk

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:144-164 checkBlockAgree
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:58-73 checkBlockAgreeF
**Official's two agreements between the members**, against
`checkBlockAgree (fueledOpsM μ)`, at closed stored types
(`checkBlockAgreeS_sim`'s `h0`/`hcvs`).  The sort comparison is `lvlEq?`,
the cached `Level.isEquiv`. -/
theorem checkBlockAgree_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (nP : Nat)
    (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal) (s0 : LIdx) (s0P : Level)
    (h0 : Expr.WScoped 0 cvTa₀P.type) :
    ∀ (cvs : List (IConstantVal × LIdx)) (cvsP : List (ConstantVal × Level)),
    (∀ x ∈ cvsP, Expr.WScoped 0 x.1.type) →
    CSpecF μ env fe
      (fun st => Frontend.denoteCV st cvTa₀ = some cvTa₀P ∧ denoteL st.ls s0 = some s0P ∧
        cvs.mapM (dCvL st) = some cvsP)
      (Arena.checkBlockAgree μ fe nP cvTa₀ s0 cvs) (fun _ _ _ => True)
      (ConLeche.checkBlockAgree (fueledOpsM μ) env nP cvTa₀P s0P cvsP) := by
  intro cvs
  induction cvs with
  | nil =>
    intro cvsP _ s₀ s' r hok hpre hrun
    obtain ⟨-, -, hcvs⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
    subst hcvs
    simp only [Arena.checkBlockAgree] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
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
    obtain ⟨o0, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, ho0⟩ := openPisAtFvarsF_run hok.state (denoteCV_type h0d) k1
    obtain ⟨tq0, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨rfl, rfl⟩ := unwrapOr_ok k2
    obtain ⟨fvs0, b0⟩ := tq0
    obtain ⟨xs0, x0, hq0, hxs0, -⟩ := denoteOpen_some_inv ho0
    -- tq
    obtain ⟨o1, s₃, k3, z3⟩ := bindOk z2
    obtain ⟨p3, ho1⟩ := openPisAtFvarsF_run p1.ok (denote_ext (denoteCV_type hxcv) p1.ext) k3
    obtain ⟨tq, s₄, k4, z4⟩ := bindOk z3
    obtain ⟨rfl, rfl⟩ := unwrapOr_ok k4
    obtain ⟨fvs1, b1⟩ := tq
    obtain ⟨xs1, x1, hq1, hxs1, -⟩ := denoteOpen_some_inv ho1
    have hxs0' := denoteEList_ext p3.ext _ _ hxs0
    have hl0 := PW.denoteEList_length hxs0'
    have hl1 := PW.denoteEList_length hxs1
    dsimp only at z4
    by_cases hlen : (fvs1.length == fvs0.length) = true
    · rw [if_pos hlen] at z4
      replace z4 := AM.pure_bind_ok z4
      obtain ⟨doms, s₅, k5, z5⟩ := bindOk z4
      obtain ⟨p5, hdoms⟩ := fvarTypeDs_run fvs0 xs0 p3.ok hxs0' k5
      have c5 := (p1.trans (p3.trans p5)).toCore hok
      obtain ⟨u6, s₆, k6, z6⟩ := bindOk z5
      obtain ⟨c6, u6v, -, fk6⟩ := checkBlockDomsAt_specF fe hk henv 0 fvs1 doms xs1
        (xs0.map Expr.fvarTypeD) (open_fvar_scope hq1 hwx)
        (fun i y hy => by
          rw [List.getElem?_map] at hy
          obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hy
          exact open_fvar_scope hq0 h0 i z hz) nP s₅ s₆ u6 c5.ok
        ⟨denoteEList_ext p5.ext _ _ hxs1, hdoms⟩ k6
      have c16 := c5.trans c6
      obtain ⟨o7, s₇, k7, z7⟩ := bindOk z6
      obtain ⟨c7, ho7⟩ := lvlEq?_crun c6.ok (denoteL_ext hxs c16.ext)
        (denoteL_ext hs0 c16.ext) k7
      obtain ⟨b8, s₈, k8, z8⟩ := bindOk z7
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
      refine FOk.bind fok_unwrapOr (FOk.bind fok_unwrapOr ?_)
      refine FOk.ite_pos (by rw [← hl0, ← hl1]; simpa using hlen)
        (FOk.bind fk6 (FOk.bind fok_liftFueled ?_))
      exact FOk.ite_pos rfl fk9
    · rw [if_neg hlen] at z4
      exact absurd z4 (AM.Never.fail_any _ _ _)

end ConRon.Bridge.Inductives
