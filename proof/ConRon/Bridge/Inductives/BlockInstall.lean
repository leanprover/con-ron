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
import ConRon.Bridge.Inductives.Positivity
import ConLeche.Verify.Cached.BlockRunC

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

/-- con-leche: none — the index spec across `consSumCtors`' pushes (none of
them a projection table). -/
theorem consSumCtors_ifenvok {st : EStore} (hwf : StoreWF st) (nP : Nat) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)) (fe : IFEnv)
      (env : Env), denoteCtors st cs = some csP → IFEnvCoh fe → IFEnvOKS env fe st →
      IFEnvOKS (ConLeche.consSumCtors nP csP env) (Arena.consSumCtors nP cs fe) st
  | [], csP, fe, env, hcs, _, h => by
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    exact h
  | (cv, n) :: cs, csP, fe, env, hcs, hcoh, h => by
    simp only [denoteCtors] at hcs
    cases hcv : Frontend.denoteCV st cv with
    | none => rw [hcv] at hcs; simp at hcs
    | some cP =>
    cases hrest : denoteCtors st cs with
    | none => rw [hcv, hrest] at hcs; simp at hcs
    | some restP =>
    rw [hcv, hrest] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    have hci : Frontend.denoteCI st (.ctorInfo cv nP n) = some (.ctorInfo cP nP n) := by
      simp only [Frontend.denoteCI, hcv, Option.map_some]
    simp only [Arena.consSumCtors, ConLeche.consSumCtors]
    refine consSumCtors_ifenvok hwf nP cs restP _ _ hrest (hcoh.push _) ?_
    intro s hs
    exact (h s hs).push ⟨by rw [hs]; exact hwf⟩ hcoh (fun t h => by cases h)
      (by rw [hs]; exact hci)

/-- con-leche: none — a list of level-handle lists survives an append. -/
theorem denoteLLists_ext {st st' : EStore} (hx : Ext st st') :
    ∀ (xs : List (List LIdx)) (ys : List (List Level)),
      denoteLLists st xs = some ys → denoteLLists st' xs = some ys
  | [], ys, h => h
  | x :: xs, ys, h => by
    simp only [denoteLLists] at h ⊢
    cases hx1 : denoteLList st.ls x with
    | none => rw [hx1] at h; simp at h
    | some y =>
    cases hxs : denoteLLists st xs with
    | none => rw [hx1, hxs] at h; simp at h
    | some ys' =>
    rw [hx1, hxs] at h
    have e1 : denoteLList st'.ls x = some y := denoteLList_ext hx.lss.ls _ _ hx1
    rw [e1, denoteLLists_ext hx xs ys' hxs]
    exact h

/-- con-leche: none — a store-preserving read is a `CoreStep`
(`Bridge/Checker/DivMod.lean`'s `CoreStep.of_store`, which this tier cannot
import). -/
theorem coreStep_of_store {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (hck : CheckOK μ env fe s) (h1 : s'.store = s.store) (h2 : s'.caches = s.caches)
    (h3 : s'.pins = s.pins) : CoreStep μ env fe s s' :=
  ⟨hck.mono ⟨by rw [h1]; exact hck.state.wf⟩ (by rw [h1]; exact Ext.refl _) h2 h3,
    by rw [h1]; exact Ext.refl _, h3⟩

/-- con-leche: none — the positivity outputs' two projections, denoted. -/
theorem dOuts_proj {st : EStore} :
    ∀ (os : List (List Arena.NestFieldKind × EIdx)) (osP : List (List ConLeche.NestFieldKind × Expr)),
      os.mapM (dOut st) = some osP →
      (os.map (·.1)).map (·.map kindOf) = osP.map (·.1) ∧
        Frontend.denoteEList st (os.map (·.2)) = some (osP.map (·.2))
  | [], osP, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  | o :: os, osP, h => by
    obtain ⟨y, ys, rfl, hy, hys⟩ := mapM_option_cons_inv h
    simp only [dOut, Option.map_eq_some_iff] at hy
    obtain ⟨e, he, rfl⟩ := hy
    obtain ⟨h1, h2⟩ := dOuts_proj os ys hys
    refine ⟨by simp only [List.map_cons] at h1 ⊢; rw [h1], ?_⟩
    simp only [List.map_cons, Frontend.denoteEList, he, h2]

theorem dOutss_proj {st : EStore} :
    ∀ (oss : List (List (List Arena.NestFieldKind × EIdx)))
      (ossP : List (List (List ConLeche.NestFieldKind × Expr))),
      dOutss st oss = some ossP →
      (oss.map (·.map (·.1))).map (·.map (·.map kindOf)) = ossP.map (·.map (·.1)) ∧
        (oss.map (·.map (·.2))).mapM (Frontend.denoteEList st) = some (ossP.map (·.map (·.2)))
  | [], ossP, h => by
    simp only [dOutss, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  | os :: oss, ossP, h => by
    simp only [dOutss] at h
    obtain ⟨y, ys, rfl, hy, hys⟩ := mapM_option_cons_inv h
    obtain ⟨h1, h2⟩ := dOuts_proj os y hy
    obtain ⟨h3, h4⟩ := dOutss_proj oss ys hys
    refine ⟨by simp only [List.map_cons] at h1 h3 ⊢; rw [h1, h3], ?_⟩
    simp only [List.map_cons]
    exact mapM_option_cons h2 h4

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
theorem anyM_dpstep {α β : Type} (d : EStore → α → Option β) (hd : DExt d)
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
    exact anyM_dpstep dCtor dCtor_ext _ hQ _ _ hin m.ctors cs s₀ s' r hok ⟨hT, hcs⟩ hrun
  exact anyM_dpstep dMember dMember_ext _ hQ _ _ hout p.shape.members ms s₀ s' r hok
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

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:166-172 consBlockInds
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:75-80 consBlockIndsF
**The formers consed**, each with its capability record: index pushes of
`.indInfo` rows on the accumulator `fe`, the records read (`blockCapsAt`) at
the caches of the ENTRY index `feC`, which the pushes do not touch.  The
answer is `InstRel` (as `consSumCtors_spec`'s) and the index spec carried
across the pushes. -/
theorem consBlockInds_spec {μ : CheckMode} {env : Env} (feC : IFEnv)
    (p₁ : Arena.BlockShape) (p₁P : ConLeche.BlockShape) (isRec : Bool) :
    ∀ (cvs : List IConstantVal) (cvsP : List ConstantVal) (i : Nat) (fe : IFEnv)
      (env' : Env), IFEnvCoh fe →
    CSpec μ env feC
      (fun st => dShape st p₁ = some p₁P ∧ cvs.mapM (Frontend.denoteCV st) = some cvsP ∧
        denoteFEnv st fe = some env')
      (Arena.consBlockInds p₁ isRec cvs i fe)
      (fun st r => InstRel fe (fun e => e = ConLeche.consBlockInds p₁P isRec cvsP i env') st r ∧
        (StoreWF st → IFEnvOKS env' fe st →
          IFEnvOKS (ConLeche.consBlockInds p₁P isRec cvsP i env') r st)) := by
  intro cvs
  induction cvs with
  | nil =>
    intro cvsP i fe env' hcoh s₀ s' r hok hpre hrun
    obtain ⟨-, hcvs, hfe⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
    subst hcvs
    simp only [Arena.consBlockInds] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, ⟨hcoh, Pushed.refl _, Nat.le_refl _, ⟨env', hfe, rfl⟩,
      ProjOut.refl _ _⟩, fun _ h => h⟩
  | cons cv rest ih =>
    intro cvsP i fe env' hcoh s₀ s' r hok hpre hrun
    obtain ⟨hp, hcvs, hfe⟩ := hpre
    obtain ⟨cvP, restP, rfl, hcv, hrest⟩ := mapM_option_cons_inv hcvs
    simp only [Arena.consBlockInds] at hrun
    obtain ⟨caps, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, hcaps⟩ := blockCapsAt_spec feC p₁ p₁P i isRec s₀ s₁ caps hok hp k1
    have x1 := c1.ext
    have hci : Frontend.denoteCI s₁.store (.indInfo cv caps) =
        some (.indInfo cvP (ConLeche.blockCapsAt p₁P i isRec)) := by
      simp only [Frontend.denoteCI, denoteCV_ext hcv x1, hcaps]
    have hpush := denoteFEnv_push (denoteFEnv_ext x1 hfe) hci
    have hnp : ∀ t, IConstantInfo.indInfo cv caps ≠ .projInfo t := fun t h => by cases h
    obtain ⟨c2, hR, hO⟩ := ih restP (i + 1) (fe.push (.indInfo cv caps))
      ⟨.indInfo cvP (ConLeche.blockCapsAt p₁P i isRec) :: env'.consts⟩ (hcoh.push _) s₁ s' r
      c1.ok ⟨dShape_ext x1 _ _ hp, dExt_denoteCV.list x1 _ _ hrest, hpush⟩ z1
    have h1 : InstRel fe (fun _ => True) s₁.store (fe.push (.indInfo cv caps)) :=
      ⟨hcoh.push _, Pushed.push _ _, Nat.le_succ _, ⟨_, hpush, trivial⟩,
        ProjOut.push hcoh _ hnp⟩
    refine ⟨c1.trans c2, InstRel.trans c2.ext h1 hR, ?_⟩
    intro hwf hS
    simp only [ConLeche.consBlockInds]
    refine hO hwf ?_
    intro s hs
    have hS' := hS s hs
    have hst : StateOK s := ⟨by rw [hs]; exact hwf⟩
    exact hS'.push hst hcoh hnp (by rw [hs]; exact denoteCI_ext hci c2.ext)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:174-187 checkBlockInds
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:82-93 checkBlockIndsF
**Stage 1**, against `checkBlockInds (fueledOpsM μ)`: the k formers checked
and agreed at the ENTRY index (so `CheckOK μ env fe` still holds at the end —
the frame is `CoreStep`), then consed.  The answer: the new index `fe₁` is an
`InstRel` of `fe` denoting con-leche's `env₁`, the index spec holds at it
(`IFEnvOKS`; with the state's `CheckOK` at `fe` this is the `ReadOK env₁ fe₁`
the caller flushes into `CheckOK μ env₁ fe₁`), the stored formers and the
completed shape denote con-leche's, and every stored former is closed
(`checkBlockIndsS_sim`'s answer). -/
theorem checkBlockInds_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (hcoh : IFEnvCoh fe) (p : Arena.BlockParts) (pP : ConLeche.BlockParts) (isRec : Bool) :
    CSpecF μ env fe
      (fun st => dParts st p = some pP ∧ denoteFEnv st fe = some env)
      (Arena.checkBlockInds μ fe p isRec)
      (fun st r v => InstRel fe (fun e => e = v.1) st r.1 ∧ IFEnvOKS v.1 r.1 st ∧
        r.2.1.mapM (Frontend.denoteCV st) = some v.2.1 ∧ dShape st r.2.2 = some v.2.2 ∧
        ∀ cv ∈ v.2.1, Expr.WScoped 0 cv.type)
      (ConLeche.checkBlockInds (fueledOpsM μ) env pP isRec) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hp, hfe⟩ := hpre
  simp only [dParts, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨ms, rs, el, sP, hms, hrs, hel, hsP, rfl⟩ := dShape_inv hq
  simp only [Arena.checkBlockInds] at hrun
  cases hmem : p.shape.members with
  | nil =>
    rw [hmem] at hrun
    exact absurd hrun (fun h => failOk h)
  | cons ms₀ rest =>
  rw [hmem] at hrun hms
  obtain ⟨ms₀P, restP, rfl, hm0, hrestP⟩ := mapM_option_cons_inv hms
  dsimp only at hrun
  obtain ⟨t1, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨c1, ⟨cvTa₀P, s0P⟩, ⟨h1a, h1b, hw1⟩, fk1⟩ := checkBlockTele_specF fe hμ hk henv
    p.shape.nP ms₀ ms₀P s₀ s₁ t1 hok ⟨hm0, hfe⟩ k1
  obtain ⟨cvTa₀, s0⟩ := t1
  dsimp only at h1a h1b z1
  obtain ⟨cvs, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨c2, cvsP, ⟨h2, hw2⟩, fk2⟩ := checkBlockTeles_specF fe hμ hk henv p.shape.nP rest
    restP s₁ s₂ cvs c1.ok ⟨dMember_ext.list c1.ext _ _ hrestP, denoteFEnv_ext c1.ext hfe⟩ k2
  have x12 := c2.ext
  obtain ⟨u3, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨c3, u3v, -, fk3⟩ := checkBlockAgree_specF fe hk henv p.shape.nP cvTa₀ cvTa₀P s0 s0P
    hw1 cvs cvsP hw2 s₂ s₃ u3 c2.ok
    ⟨denoteCV_ext h1a x12, denoteL_ext h1b x12, h2⟩ k3
  have c13 := c1.trans (c2.trans c3)
  obtain ⟨p₁, s₄, k4, z4⟩ := bindOk z3
  obtain ⟨c4, hp₁⟩ := BlockShape.withSort_spec fe p.shape
    ⟨ms₀P :: restP, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩ s0 s0P s₃ s₄ p₁
    c3.ok ⟨dShape_ext c13.ext _ _ hq, denoteL_ext h1b (c2.ext.trans c3.ext)⟩ k4
  have c14 := c13.trans c4
  obtain ⟨fe₁, s₅, k5, z5⟩ := bindOk z4
  have hcvTas : (cvTa₀ :: cvs.map (·.1)).mapM (Frontend.denoteCV s₄.store) =
      some (cvTa₀P :: cvsP.map (·.1)) := by
    refine mapM_option_cons (denoteCV_ext h1a (c2.ext.trans (c3.ext.trans c4.ext))) ?_
    have h2' := dCvL_ext.list (c3.ext.trans c4.ext) _ _ h2
    clear h2 hw2 fk2 fk3 k2 k3 z2 z3 z4 z5 k5
    generalize cvs = xs at h2'
    generalize cvsP = ys at h2'
    induction xs generalizing ys with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h2'
      subst h2'; rfl
    | cons x xs ih =>
      obtain ⟨y, ys', rfl, hy, hys⟩ := mapM_option_cons_inv h2'
      exact mapM_option_cons (dCvL_inv hy).1 (ih ys' hys)
  obtain ⟨c5, hR, hO⟩ := consBlockInds_spec fe p₁ _ isRec _ _ 0 fe env hcoh s₄ s₅ fe₁ c4.ok
    ⟨hp₁, hcvTas, denoteFEnv_ext c14.ext hfe⟩ k5
  obtain ⟨rfl, rfl⟩ := pureOk z5
  have c15 := c14.trans c5
  refine ⟨c15, (ConLeche.consBlockInds (ConLeche.BlockShape.withSort
      ⟨ms₀P :: restP, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩ s0P) isRec
      (cvTa₀P :: cvsP.map (·.1)) 0 env, cvTa₀P :: cvsP.map (·.1),
      ConLeche.BlockShape.withSort
      ⟨ms₀P :: restP, rs, p.shape.nP, el, sP, p.shape.large, p.shape.isProp⟩ s0P),
    ⟨hR, hO c5.ok.state.wf (c5.ok.ienv.toS), dExt_denoteCV.list c5.ext _ _ hcvTas,
    dShape_ext c5.ext _ _ hp₁, ?_⟩, ?_⟩
  · intro cv hcv
    rcases List.mem_cons.mp hcv with rfl | hcv
    · exact hw1
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hcv
      exact hw2 y hy
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
  obtain ⟨ms, rs, el, sP, -, -, -, hsP, rfl⟩ := dShape_inv hp
  simp only [Arena.BlockShape.nestCtx] at hrun
  obtain ⟨lv, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hlv⟩ := paramLevels_spec p.lps _ s₀ s₁ lv hok hlps k1
  obtain ⟨rfl, rfl⟩ := pureOk z1
  refine ⟨p1, ?_⟩
  have x := p1.ext
  simp only [dCtx, denoteNListE_ext x _ _ hnames, denoteNListE_ext x _ _ hlps,
    denoteEList_ext x _ _ hfvs, denoteL_ext hsP x, hlv, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, if_true, ConLeche.BlockShape.nestCtx, hnI]

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:199-210 checkBlockCtors
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:97-106 checkBlockCtorsF
**The constructors of every member**, against
`checkBlockCtors (fueledOpsM μ) env₀ env pP (msP.zip cvsP)`: the twin's two
side-by-side lists stop at the shorter, as `zip` does.  The formers' stored
types are closed (`checkBlockCtorsS_sim`'s `hl`). -/
theorem checkBlockCtors_specF {μ : CheckMode} {env : Env} (fe₀ fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (env₀ : Env) :
    ∀ (mss : List Arena.MemberShape) (mssP : List ConLeche.MemberShape)
      (cvs : List IConstantVal) (cvsP : List ConstantVal),
    (∀ cv ∈ cvsP, Expr.WScoped 0 cv.type) →
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ mss.mapM (dMember st) = some mssP ∧
        cvs.mapM (Frontend.denoteCV st) = some cvsP ∧
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env ∧
        IFEnvOKS env₀ fe₀ st)
      (Arena.checkBlockCtors μ fe₀ fe p mss cvs)
      (fun st r v => r.1.mapM (dCtors st) = some v.1 ∧ r.2.mapM (denoteLLists st) = some v.2)
      (ConLeche.checkBlockCtors (fueledOpsM μ) env₀ env pP (mssP.zip cvsP)) := by
  intro mss
  induction mss with
  | nil =>
    intro mssP cvs cvsP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hms, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.checkBlockCtors] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, ([], []), ⟨rfl, rfl⟩, by
      simp only [List.zip_nil_left, ConLeche.checkBlockCtors]; exact FOk.pure _⟩
  | cons ms rest ih =>
    intro mssP cvs cvsP hws s₀ s' r hok hpre hrun
    obtain ⟨hp, hms, hcvs, hfe₀, hfe, hok₀⟩ := hpre
    obtain ⟨msP, restP, rfl, hm, hrest⟩ := mapM_option_cons_inv hms
    cases cvs with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
      subst hcvs
      simp only [Arena.checkBlockCtors] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, ([], []), ⟨rfl, rfl⟩, by
        simp only [List.zip_nil_right, ConLeche.checkBlockCtors]; exact FOk.pure _⟩
    | cons cvTa cvTas =>
    obtain ⟨cvTaP, cvTasP, rfl, hcv, hcvs'⟩ := mapM_option_cons_inv hcvs
    obtain ⟨cvT, csP, hcvT, hcs, rfl⟩ := dMember_inv hm
    have hlps := BlockShape.lps_spec hp
    obtain ⟨mm, rs, el, sP, -, -, -, hsP, rfl⟩ := dShape_inv hp
    simp only [Arena.checkBlockCtors] at hrun
    obtain ⟨t1, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, ⟨csA, ssA⟩, ⟨h1a, h1b⟩, fk1⟩ := checkSumCtors_specF fe₀ fe hμ hk henv
      ms.cvT.name cvT.name p.lps _ p.nP ms.nIdx p.resSort sP p.isProp p.large cvTa cvTaP env₀
      ms.ctors csP (ConLeche.Cached.ws0_hasFvar (hws _ List.mem_cons_self)) s₀ s₁ t1 hok
      ⟨denoteCV_name hcvT, hlps, hsP, hcv, by rw [← dCtors_eq_denoteCtors]; exact hcs,
        hfe₀, hfe, hok₀⟩ k1
    obtain ⟨cs, ss⟩ := t1
    dsimp only at h1a h1b z1
    have x1 := c1.ext
    obtain ⟨t2, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨c2, ⟨restC, restS⟩, ⟨h2a, h2b⟩, fk2⟩ := ih restP cvTas cvTasP
      (fun cv h => hws cv (List.mem_cons_of_mem _ h)) s₁ s₂ t2 c1.ok
      ⟨dShape_ext x1 _ _ hp, dMember_ext.list x1 _ _ hrest, dExt_denoteCV.list x1 _ _ hcvs',
        denoteFEnv_ext x1 hfe₀, denoteFEnv_ext x1 hfe, hok₀.mono x1⟩ k2
    obtain ⟨rC, rS⟩ := t2
    dsimp only at h2a h2b z2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨c1.trans c2, (csA :: restC, ssA :: restS), ⟨?_, ?_⟩, ?_⟩
    · refine mapM_option_cons ?_ h2a
      rw [dCtors_eq_denoteCtors]
      exact denoteCtors_ext c2.ext _ _ h1a
    · refine mapM_option_cons ?_ h2b
      exact denoteLLists_ext c2.ext _ _ h1b
    · simp only [List.zip_cons_cons]
      unfold ConLeche.checkBlockCtors
      exact FOk.bind fk1 (FOk.bind fk2 (FOk.pure _))

/-- con-leche: ConLeche/Verify/Cached/BlockRunC.lean:503-523 checkBlockCtors_types
The constructors' stage stores closed constructor types — the fact the
positivity stage needs (`checkBlockPositivityS_sim`'s `hct`), off the pure
run `FOk` hands over. -/
theorem checkBlockCtors_types {μ : CheckMode} {env₀ env : Env} {q : ConLeche.BlockShape}
    {l : List (ConLeche.MemberShape × ConstantVal)}
    {v : List (List (ConstantVal × Nat)) × List (List (List Level))}
    (h : FOk (ConLeche.checkBlockCtors (fueledOpsM μ) env₀ env q l) v) :
    ∀ ctorsA ∈ v.1, ∀ c ∈ ctorsA, Expr.WScoped 0 c.1.type := by
  obtain ⟨F, hF⟩ := h
  rw [checkBlockCtors_datF] at hF
  exact ConLeche.Cached.checkBlockCtors_types hF

/-- con-leche: ConLeche/Verify/Cached/BlockRunC.lean:525-546 checkBlockCtors_fresh
The constructors' stage stores constructors fresh in its environment. -/
theorem checkBlockCtors_fresh {μ : CheckMode} {env₀ env : Env} {q : ConLeche.BlockShape}
    {l : List (ConLeche.MemberShape × ConstantVal)}
    {v : List (List (ConstantVal × Nat)) × List (List (List Level))}
    (h : FOk (ConLeche.checkBlockCtors (fueledOpsM μ) env₀ env q l) v) :
    ∀ ctorsA ∈ v.1, ∀ c ∈ ctorsA, env.find? c.1.name = none := by
  obtain ⟨F, hF⟩ := h
  rw [checkBlockCtors_datF] at hF
  exact ConLeche.Cached.checkBlockCtors_fresh hF

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:228-250 checkAbsCtorSorts
**The fields' universes at the holes**, against
`checkAbsCtorSorts (fueledOpsM μ) env ctxP`, pairwise to the shorter list.
The twin's `isProp` (read once by the caller) is con-leche's per-call
`Level.isEquiv ctxP.sort .zero == some true` (`hprop`); the normal forms are
scoped at the holes' depth (`checkAbsCtorSortsS_sim`'s `hos`). -/
theorem checkAbsCtorSorts_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) (isProp : Bool)
    (hprop : isProp = (Level.isEquiv ctxP.sort .zero == some true)) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
      (os : List (List Arena.NestFieldKind × EIdx)) (osP : List (List ConLeche.NestFieldKind × Expr)),
    (∀ o ∈ osP, Expr.WScoped (ctxP.hiAt 0) o.2) →
    CSpecF μ env fe
      (fun st => dCtx st ctxP.find? ctx = some ctxP ∧ dCtors st cs = some csP ∧
        os.mapM (dOut st) = some osP ∧ denoteFEnv st fe = some env)
      (Arena.checkAbsCtorSorts μ fe ctx isProp cs os) (fun _ _ _ => True)
      (ConLeche.checkAbsCtorSorts (fueledOpsM μ) env ctxP csP osP) := by
  intro cs
  induction cs with
  | nil =>
    intro csP os osP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hcs, -⟩ := hpre
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.checkAbsCtorSorts] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, (), trivial, by
      simp only [ConLeche.checkAbsCtorSorts]; exact FOk.pure ()⟩
  | cons c cs ih =>
    intro csP os osP hws s₀ s' r hok hpre hrun
    obtain ⟨hctx, hcs, hos, hfe⟩ := hpre
    obtain ⟨cP, csP', rfl, hc, hcs'⟩ := mapM_option_cons_inv hcs
    cases os with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hos
      subst hos
      simp only [Arena.checkAbsCtorSorts] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
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
    obtain ⟨namesP, lpsP, paramsP, sortP, hceq, hn, hl, -, hsort, -⟩ := dCtx_inv hctx
    have hl' : Frontend.denoteNList s₀.store.ns ctx.lps = some ctxP.lps := by rw [hceq]; exact hl
    have hsort' : denoteL s₀.store.ls ctx.sort = some ctxP.sort := by rw [hceq]; exact hsort
    have hhi : ctx.hiAt 0 = ctxP.hiAt 0 := by
      rw [hceq]
      simp [Arena.NestCtx.hiAt, ConLeche.NestCtx.hiAt, PW.denoteNList_length hn]
    simp only [Arena.checkAbsCtorSorts] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨h1s, h1c, h1p, hb⟩ := allLevelParamsDefined_run hok.state hl' htyN k1
    have c1 := coreStep_of_store hok h1s h1c h1p
    obtain ⟨hbt, z2⟩ := AM.dunless_ok AM.Never.fail_any z1
    replace z2 := AM.pure_bind_ok z2
    obtain ⟨oq, s₂, k2, z3⟩ := bindOk z2
    obtain ⟨p2, hoq⟩ := openPisAtFvarsF_run c1.ok.state
      (denote_ext htyN c1.ext) k2
    obtain ⟨xq, s₃, k3, z4⟩ := bindOk z3
    obtain ⟨rfl, hs3⟩ := unwrapOr_ok k3
    subst s₃
    obtain ⟨fvs, rest⟩ := xq
    obtain ⟨xsP, xP, hxq, hxs, -⟩ := denoteOpen_some_inv hoq
    rw [hhi] at hxq
    have c2 := c1.trans (p2.toCore c1.ok)
    obtain ⟨u5, s₅, k5, z5⟩ := bindOk z4
    have hfvsc := open_fvar_scope hxq hW
    obtain ⟨c5, u5v, -, fk5⟩ := checkStructFieldSortsI_specF fe hk henv isProp false ctx.sort
      ctxP.sort (ctx.hiAt 0) fvs [] xsP [] c.2 (by rw [hhi]; exact hfvsc) s₂ s₅ u5 c2.ok
      ⟨denoteL_ext hsort' c2.ext, hxs, rfl, denoteFEnv_ext c2.ext hfe⟩ k5
    have c25 := c2.trans c5
    obtain ⟨c6, u6, -, fk6⟩ := ih csP' os osP' (fun y hy => hws y (List.mem_cons_of_mem _ hy))
      s₅ s' r c5.ok ⟨dCtx_ext _ c25.ext _ _ hctx, dCtors_ext c25.ext _ _ hcs',
        dOut_ext.list c25.ext _ _ hos', denoteFEnv_ext c25.ext hfe⟩ z5
    refine ⟨c25.trans c6, (), trivial, ?_⟩
    rw [hb] at hbt
    unfold ConLeche.checkAbsCtorSorts
    simp only [hxq]
    refine FOk.ite_pos hbt (FOk.bind fok_unwrapOr ?_)
    rw [← hprop, ← hhi]
    exact FOk.bind fk5 fk6

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:252-258 checkAbsCtorSortsAll
`checkAbsCtorSorts` on every member's constructors (`checkAbsCtorSortsAllS_sim`). -/
theorem checkAbsCtorSortsAll_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (ctx : Arena.NestCtx) (ctxP : ConLeche.NestCtx) (isProp : Bool)
    (hprop : isProp = (Level.isEquiv ctxP.sort .zero == some true)) :
    ∀ (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat)))
      (oss : List (List (List Arena.NestFieldKind × EIdx)))
      (ossP : List (List (List ConLeche.NestFieldKind × Expr))),
    (∀ os ∈ ossP, ∀ o ∈ os, Expr.WScoped (ctxP.hiAt 0) o.2) →
    CSpecF μ env fe
      (fun st => dCtx st ctxP.find? ctx = some ctxP ∧ css.mapM (dCtors st) = some cssP ∧
        dOutss st oss = some ossP ∧ denoteFEnv st fe = some env)
      (Arena.checkAbsCtorSortsAll μ fe ctx isProp css oss) (fun _ _ _ => True)
      (ConLeche.checkAbsCtorSortsAll (fueledOpsM μ) env ctxP cssP ossP) := by
  intro css
  induction css with
  | nil =>
    intro cssP oss ossP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hcs, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.checkAbsCtorSortsAll] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, (), trivial, by
      simp only [ConLeche.checkAbsCtorSortsAll]; exact FOk.pure ()⟩
  | cons cs css ih =>
    intro cssP oss ossP hws s₀ s' r hok hpre hrun
    obtain ⟨hctx, hcss, hoss, hfe⟩ := hpre
    simp only [dOutss] at hoss
    obtain ⟨csP, cssP', rfl, hc, hcss'⟩ := mapM_option_cons_inv hcss
    cases oss with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hoss
      subst hoss
      simp only [Arena.checkAbsCtorSortsAll] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, (), trivial, by
        simp only [ConLeche.checkAbsCtorSortsAll]; exact FOk.pure ()⟩
    | cons os oss =>
    obtain ⟨osP, ossP', rfl, ho, hoss'⟩ := mapM_option_cons_inv hoss
    simp only [Arena.checkAbsCtorSortsAll] at hrun
    obtain ⟨u1, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, u1v, -, fk1⟩ := checkAbsCtorSorts_specF fe hk henv ctx ctxP isProp hprop cs csP
      os osP (hws osP List.mem_cons_self) s₀ s₁ u1 hok ⟨hctx, hc, ho, hfe⟩ k1
    have x1 := c1.ext
    obtain ⟨c2, u2, -, fk2⟩ := ih cssP' oss ossP' (fun y hy => hws y (List.mem_cons_of_mem _ hy))
      s₁ s' r c1.ok ⟨dCtx_ext _ x1 _ _ hctx, dCtors_ext.list x1 _ _ hcss',
        dOutss_ext x1 _ _ hoss', denoteFEnv_ext x1 hfe⟩ z1
    refine ⟨c1.trans c2, (), trivial, ?_⟩
    unfold ConLeche.checkAbsCtorSortsAll
    exact FOk.bind fk1 fk2

/-! ## Stage 2: the tail -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:298-311 checkBlockIdxSorts
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:110-120 checkBlockIdxSortsF
**Every member's index binders' universes**, against
`checkBlockIdxSorts (fueledOpsM μ) env₁ pP (msP.zip cvsP)`, at closed stored
formers (`checkBlockIdxSortsS_sim`'s `hl`). -/
theorem checkBlockIdxSorts_specF {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) :
    ∀ (mss : List Arena.MemberShape) (mssP : List ConLeche.MemberShape)
      (cvs : List IConstantVal) (cvsP : List ConstantVal),
    (∀ cv ∈ cvsP, Expr.WScoped 0 cv.type) →
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ mss.mapM (dMember st) = some mssP ∧
        cvs.mapM (Frontend.denoteCV st) = some cvsP ∧ denoteFEnv st fe = some env)
      (Arena.checkBlockIdxSorts μ fe p mss cvs)
      (fun st r v => denoteLLists st r = some v)
      (ConLeche.checkBlockIdxSorts (fueledOpsM μ) env pP (mssP.zip cvsP)) := by
  intro mss
  induction mss with
  | nil =>
    intro mssP cvs cvsP _ s₀ s' r hok hpre hrun
    obtain ⟨-, hms, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.checkBlockIdxSorts] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], rfl, by
      simp only [List.zip_nil_left, ConLeche.checkBlockIdxSorts]; exact FOk.pure _⟩
  | cons ms rest ih =>
    intro mssP cvs cvsP hws s₀ s' r hok hpre hrun
    obtain ⟨hp, hms, hcvs, hfe⟩ := hpre
    obtain ⟨msP, restP, rfl, hm, hrest⟩ := mapM_option_cons_inv hms
    cases cvs with
    | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
      subst hcvs
      simp only [Arena.checkBlockIdxSorts] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, [], rfl, by
        simp only [List.zip_nil_right, ConLeche.checkBlockIdxSorts]; exact FOk.pure _⟩
    | cons cvTa cvTas =>
    obtain ⟨cvTaP, cvTasP, rfl, hcv, hcvs'⟩ := mapM_option_cons_inv hcvs
    obtain ⟨cvT, csP, -, -, rfl⟩ := dMember_inv hm
    obtain ⟨mm, rs, el, sP, -, -, -, hsP, rfl⟩ := dShape_inv hp
    have hw : Expr.WScoped 0 cvTaP.type := hws _ List.mem_cons_self
    simp only [Arena.checkBlockIdxSorts] at hrun
    obtain ⟨oq, s₁, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hoq⟩ := openPisAtFvarsF_run hok.state (denoteCV_type hcv) k1
    obtain ⟨tq, s₂, k2, z2⟩ := bindOk z1
    obtain ⟨rfl, hs2⟩ := unwrapOr_ok k2
    subst s₂
    obtain ⟨fvs, b⟩ := tq
    obtain ⟨xsP, xP, htq, hxs, -⟩ := denoteOpen_some_inv hoq
    have c1 := p1.toCore hok
    obtain ⟨is, s₃, k3, z3⟩ := bindOk z2
    have hxPos : ∀ (i : Nat) (x : Expr), (xsP.drop p.nP)[i]? = some x →
        Expr.WScoped (p.nP + i) x.fvarTypeD := by
      intro i x hx
      rw [List.getElem?_drop] at hx
      have := open_fvar_scope htq hw (p.nP + i) x hx
      simpa using this
    obtain ⟨c3, isP, h3, fk3⟩ := checkStructFieldSortsI_specF fe hk henv true false p.resSort sP
      p.nP (fvs.drop p.nP) [] (xsP.drop p.nP) [] ms.nIdx hxPos s₁ s₃ is c1.ok
      ⟨denoteL_ext hsP c1.ext, denoteEList_drop hxs p.nP, rfl, denoteFEnv_ext c1.ext hfe⟩ k3
    have c13 := c1.trans c3
    obtain ⟨rs', s₄, k4, z4⟩ := bindOk z3
    obtain ⟨c4, rsP, h4, fk4⟩ := ih restP cvTas cvTasP (fun cv h => hws cv (List.mem_cons_of_mem _ h))
      s₃ s₄ rs' c3.ok ⟨dShape_ext c13.ext _ _ hp, dMember_ext.list c13.ext _ _ hrest,
        dExt_denoteCV.list c13.ext _ _ hcvs', denoteFEnv_ext c13.ext hfe⟩ k4
    obtain ⟨rfl, rfl⟩ := pureOk z4
    refine ⟨c13.trans c4, isP :: rsP, ?_, ?_⟩
    · have e3 : denoteLList s'.store.ls is = some isP := denoteLList_ext c4.ext.lss.ls _ _ h3
      simp only [denoteLLists, e3, h4]
    · simp only [List.zip_cons_cons]
      unfold ConLeche.checkBlockIdxSorts
      simp only [htq]
      exact FOk.bind fok_unwrapOr (FOk.bind fk3 (FOk.bind fk4 (FOk.pure _)))

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:313-317 consBlockCtors
con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:122-125 consBlockCtorsF
**The members' constructors consed**, member by member.  PURE on both sides:
`InstRel` (over `consSumCtors_spec`), and the index spec carried across the
pushes (none a projection table) — what the caller's flush needs. -/
theorem consBlockCtors_spec (st : EStore) (nP : Nat) :
    ∀ (css : List (List (IConstantVal × Nat))) (cssP : List (List (ConstantVal × Nat)))
      (fe : IFEnv) (env : Env), css.mapM (dCtors st) = some cssP →
      denoteFEnv st fe = some env → IFEnvCoh fe →
      InstRel fe (fun e => e = ConLeche.consBlockCtors nP cssP env) st
        (Arena.consBlockCtors nP css fe) ∧
      (StoreWF st → IFEnvOKS env fe st →
        IFEnvOKS (ConLeche.consBlockCtors nP cssP env) (Arena.consBlockCtors nP css fe) st)
  | [], cssP, fe, env, hcss, hfe, hcoh => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcss
    subst hcss
    exact ⟨⟨hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, rfl⟩, ProjOut.refl _ _⟩,
      fun _ h => h⟩
  | cs :: css, cssP, fe, env, hcss, hfe, hcoh => by
    obtain ⟨csP, cssP', rfl, hcs, hcss'⟩ := mapM_option_cons_inv hcss
    rw [dCtors_eq_denoteCtors] at hcs
    have h1 := consSumCtors_spec st nP cs csP fe env hcs hfe hcoh
    obtain ⟨e1, he1, rfl⟩ := h1.denote
    obtain ⟨h2, hO⟩ := consBlockCtors_spec st nP css cssP' _ _ hcss' he1 h1.coh
    refine ⟨InstRel.trans (Ext.refl _) h1 h2, fun hwf hS => ?_⟩
    exact hO hwf (consSumCtors_ifenvok hwf nP cs csP fe env hcs hcoh hS)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:260-274 blockNestCtx
**The walk's context** of a block, against
`blockNestCtx (m := FueledM) pP cvsP env.find?`, the lookup the environment
(the index's spec, `nestHoles_spec`), with the scoping facts
`blockNestCtxS_sim` states of it: the context's stored constants closed, the
holes variables scoped at the holes' depth, the canonical variables scoped
there and one per parameter. -/
theorem blockNestCtx_spec {μ : CheckMode} {env : Env} (fe : IFEnv) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (cvs : List IConstantVal)
    (cvsP : List ConstantVal) (hT : ∀ cv ∈ cvsP, Expr.WScoped 0 cv.type) :
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ cvs.mapM (Frontend.denoteCV st) = some cvsP)
      (Arena.blockNestCtx fe p cvs)
      (fun st r v => dCtx st env.find? r.1 = some v.1 ∧ Frontend.denoteEList st r.2 = some v.2 ∧
        NestCtxOk v.1 ∧ (∀ x ∈ v.2, Expr.WScoped (v.1.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty) ∧
        (∀ x ∈ v.1.params, Expr.WScoped (v.1.hiAt 0) x) ∧ v.1.params.length = v.1.nP ∧
        ConLeche.nestHoles v.1 = some v.2 ∧ v.1.nP = pP.nP)
      (ConLeche.blockNestCtx (m := FueledM) pP cvsP env.find?) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hp, hcvs⟩ := hpre
  simp only [Arena.blockNestCtx] at hrun
  cases cvs with
  | nil => exact absurd hrun (fun h => failOk h)
  | cons cv0 rest =>
  obtain ⟨cv0P, restP, rfl, hcv0, -⟩ := mapM_option_cons_inv hcvs
  have hnP : p.nP = pP.nP := by
    obtain ⟨_, _, _, _, -, -, -, -, rfl⟩ := dShape_inv hp; rfl
  dsimp only at hrun
  obtain ⟨o, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := openPisAtFvarsF_run hok.state (denoteCV_type hcv0) k1
  obtain ⟨pq, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨rfl, hs2⟩ := unwrapOr_ok k2
  subst s₂
  obtain ⟨fvs, b⟩ := pq
  obtain ⟨xs, x, hpq, hxs, -⟩ := denoteOpen_some_inv ho
  rw [hnP] at hpq
  obtain ⟨ctx, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨p3, hctx⟩ := BlockShape.nestCtx_spec p pP fvs xs env.find? s₁ s₃ ctx p1.ok
    ⟨dShape_ext p1.ext _ _ hp, hxs⟩ k3
  have p13 := p1.trans p3
  obtain ⟨oh, s₄, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hoh⟩ := nestHoles_spec (env := env) (fe := fe) ctx _ s₃ s₄ oh p13.ok
    ⟨(p13.toCore hok).ok.ienv.toS, hctx⟩ k4
  obtain ⟨holes, s₅, k5, z5⟩ := bindOk z4
  obtain ⟨rfl, hs5⟩ := unwrapOr_ok k5
  subst s₅
  obtain ⟨rfl, rfl⟩ := pureOk z5
  obtain ⟨holesP, hnh, hholes⟩ := hoh
  have hw0 : Expr.WScoped 0 cv0P.type := hT _ List.mem_cons_self
  have hctxOk : NestCtxOk (pP.nestCtx xs env.find?) :=
    fun n ci hf => (henv ci (List.mem_of_find?_eq_some hf)).1
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
  simp only [List.head?_cons]
  refine FOk.bind fok_unwrapOr ?_
  simp only [hpq]
  refine FOk.bind fok_unwrapOr ?_
  simp only [hnh]
  exact FOk.bind fok_unwrapOr (FOk.pure _)

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:276-294 checkBlockPositivity
**The block's positivity, on its stored constructors**, against
`checkBlockPositivity (fueledOpsM μ) env env.find? pP cvsP ctorsAsP` (the
twin's lookup is the environment `fe`): the walk's context
(`blockNestCtx_spec`), the uniform-occurrence check (`nestUniform_spec`), the
root frame (`nestRoot_spec`), the fields' universes (`checkAbsCtorSortsAll`,
the twin's `isProp` read once through `lvlEq?`).  The formers' and the
constructors' stored types are closed (`checkBlockPositivityS_sim`'s `hT`,
`hct`; `checkBlockInds_spec`'s answer and `checkBlockCtors_types`). -/
theorem checkBlockPositivity_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockParts) (pP : ConLeche.BlockParts) (cvs : List IConstantVal)
    (cvsP : List ConstantVal) (ctorsAs : List (List (IConstantVal × Nat)))
    (ctorsAsP : List (List (ConstantVal × Nat)))
    (hT : ∀ cv ∈ cvsP, Expr.WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAsP, ∀ c ∈ ctorsA, Expr.WScoped 0 c.1.type) :
    CSpecF μ env fe
      (fun st => dParts st p = some pP ∧ cvs.mapM (Frontend.denoteCV st) = some cvsP ∧
        ctorsAs.mapM (dCtors st) = some ctorsAsP ∧ denoteFEnv st fe = some env)
      (Arena.checkBlockPositivity μ fe p cvs ctorsAs)
      (fun st r v => r.1.map (·.map (·.map kindOf)) = v.1 ∧
        r.2.1.mapM (Frontend.denoteEList st) = some v.2.1 ∧ dState st r.2.2 = some v.2.2)
      (ConLeche.checkBlockPositivity (fueledOpsM μ) env env.find? pP cvsP ctorsAsP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hp, hcvs, hcas, hfe⟩ := hpre
  simp only [dParts, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hcl : ∀ cs ∈ ctorsAsP, ∀ c ∈ cs, c.1.type.hasFvar = false :=
    fun cs hcs c hc => ConLeche.Cached.ws0_hasFvar (hct cs hcs c hc)
  simp only [Arena.checkBlockPositivity] at hrun
  obtain ⟨t1, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨c1, ⟨ctxP, holesP⟩, ⟨hctx, hholes, hctxOk, hhw, hpar, -, hnh, -⟩, fk1⟩ :=
    blockNestCtx_spec fe henv p.shape q cvs cvsP hT s₀ s₁ t1 hok ⟨hq, hcvs⟩ k1
  obtain ⟨ctx, holes⟩ := t1
  dsimp only at hctx hholes hhw hpar hnh z1
  have x1 := c1.ext
  obtain ⟨u2, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨c2, u2v, -, fk2⟩ := nestUniform_spec env.find? ctx ctxP ctorsAs ctorsAsP s₁ s₂ u2
    c1.ok ⟨hctx, dCtors_ext.list x1 _ _ hcas⟩ k2
  have x12 := c1.ext.trans c2.ext
  obtain ⟨t3, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨c3, ⟨outsP, nsP⟩, ⟨houts, hns, hwN⟩, fk3⟩ := nestRoot_spec hk henv hctxOk holes holesP
    (fun y hy => (hhw y hy).1) (by rw [ConLeche.nestHoles_length hnh]; exact Nat.le_refl _) hpar ctorsAs ctorsAsP
    {} {} [] [] hcl s₂ s₃ t3 c2.ok
    ⟨dCtx_ext _ c2.ext _ _ hctx, denoteEList_ext c2.ext _ _ hholes,
      dCtors_ext.list x12 _ _ hcas, by simp [dState], rfl⟩ k3
  obtain ⟨outs, ns⟩ := t3
  simp only [List.nil_append] at houts
  dsimp only at houts hns z3
  have x13 := x12.trans c3.ext
  obtain ⟨z, s₄, k4, z4⟩ := bindOk z3
  obtain ⟨hs4, hz⟩ := zeroLevel_run c3.ok.pins k4
  subst s₄
  obtain ⟨ov, s₅, k5, z5⟩ := bindOk z4
  obtain ⟨namesP, lpsP, paramsP, sortP, hceq, -, -, -, hsort, -⟩ := dCtx_inv hctx
  have hfind : ctxP.find? = env.find? := by rw [hceq]
  have hsort' : denoteL s₃.store.ls ctx.sort = some ctxP.sort := by
    rw [hceq]; exact denoteL_ext hsort (c2.ext.trans c3.ext)
  obtain ⟨c5, hov⟩ := lvlEq?_crun c3.ok hsort' hz k5
  have x15 := x13.trans c5.ext
  obtain ⟨u6, s₆, k6, z6⟩ := bindOk z5
  obtain ⟨c6, u6v, -, fk6⟩ := checkAbsCtorSortsAll_specF fe hk henv ctx ctxP _ (by rw [hov])
    ctorsAs ctorsAsP outs outsP hwN s₅ s₆ u6 c5.ok
    ⟨by rw [hfind]; exact dCtx_ext _ ((c2.ext.trans c3.ext).trans c5.ext) _ _ hctx,
      dCtors_ext.list x15 _ _ hcas, dOutss_ext c5.ext _ _ houts,
      denoteFEnv_ext x15 hfe⟩ k6
  obtain ⟨rfl, rfl⟩ := pureOk z6
  obtain ⟨hp1, hp2⟩ := dOutss_proj outs outsP (dOutss_ext (c5.ext.trans c6.ext) _ _ houts)
  refine ⟨(((c1.trans c2).trans c3).trans c5).trans c6,
    (outsP.map (·.map (·.1)), outsP.map (·.map (·.2)), nsP),
    ⟨hp1, hp2, dState_ext (c5.ext.trans c6.ext) _ _ hns⟩, ?_⟩
  unfold ConLeche.checkBlockPositivity
  exact FOk.bind fk1 (FOk.bind fk2 (FOk.bind fk3 (FOk.bind fk6 (FOk.pure _))))

end ConRon.Bridge.Inductives
