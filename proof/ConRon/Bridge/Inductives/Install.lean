/-
# `ConRon.Bridge.Inductives.Install` — Theorem 1 for what a block installs

`Arena/Install.lean`'s block half against `ConLeche/Kernel/Install.lean`: the
formers with their capability records (`blockCapsAt`, `blockFormers`), the
constructors (`blockCtors`), the recursors with their rules' firing mode
(`Expr.dropVars`, `recFire`, `blockRecs`), the projection tables
(`blockTables`), the block's constants (`blockConstants`, at official's
`is_rec`, `blockIsRec`), and the recogniser at this frame (`blockShape?`).

**Pure grade throughout but the recogniser.**  Nothing here reads the
environment: the twins read the record, intern and walk handles, so every
statement is a run form at `PStep` (state invariant, append, cache frame,
untouched pins).  `blockShape?` is the exception: its `isProp` is `lvlEq?`'s
cached verdict, the denotation only under `CheckOK`'s cache clauses
(`Bridge/Inductives/BlockShape.lean`'s module note).

These feed the stream index (`Arena/StreamIndex.lean`'s `buildIndex` reads
`declConstants`/`declTables` of every record before any check) and nothing in
the block's check: the check's own install is dropped with the job's index.
-/
module

import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Inductives.StructParts
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.ExprOps.Inst1
import ConRon.Bridge.ExprOps.Subst
public import ConRon.Bridge.Inductives.Rel
/- `simp only` unfolds the toolchain's monadic list functions (`List.anyM`),
whose bodies `Init.Data.List.Control` does not expose. -/
import all Init.Data.List.Control
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.Inductives.NestScope
public import ConRon.Arena.Install

public section

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The capability record -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:67-81 blockCapsAt
**The capability record of member `mi`**, exactly: pure on both sides, read
off the record.  The default member's `etaCtor` is the zero handle,
`.anonymous` under `PinsOK.anon`. -/
theorem blockCapsAt_denote {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (hanon : denoteN st.ns (default : NIdx) = some ConLeche.Name.anonymous)
    (hp : dShape st p = some pP) (mi : Nat) (isRec : Bool) :
    Frontend.denoteCaps st (Arena.blockCapsAt p mi isRec)
      = some (ConLeche.blockCapsAt pP mi isRec) := by
  have hnames := BlockShape.memberNames_spec hp
  obtain ⟨hms, -, hnP, -, -, -, -⟩ := dShape_inv hp
  have hg := mapM_option_getElem?_bind hms mi
  simp only [Arena.blockCapsAt]
  simp only [ConLeche.blockCapsAt, List.getD_eq_getElem?_getD]
  cases hmi : p.members[mi]? with
  | none =>
    rw [hmi] at hg
    simp only [Option.bind_none] at hg
    rw [hg]
    simp only [Option.getD_none]
    simp only [Frontend.denoteCaps, hanon, hnames, hnP, Frontend.denoteNList]
    rfl
  | some m =>
    rw [hmi] at hg
    simp only [Option.bind_some] at hg
    obtain ⟨mP, hmP⟩ : ∃ mP, dMember st m = some mP := by
      cases h : dMember st m with
      | none =>
        exfalso
        rw [h] at hg
        have h1 := List.getElem?_eq_none_iff.mp hg
        obtain ⟨h2, -⟩ := List.getElem?_eq_some_iff.mp hmi
        have hl := ConLeche.option_mapM_length hms
        omega
      | some mP => exact ⟨mP, rfl⟩
    rw [hmP] at hg
    rw [hg]
    simp only [Option.getD_some]
    obtain ⟨cv, dv, nI, cs⟩ := mP
    obtain ⟨-, rfl, hcs, -⟩ := dMember_inv hmP
    dsimp only at hcs ⊢
    cases hc : m.ctors with
    | nil =>
      rw [hc] at hcs
      simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
      subst hcs
      simp only [Frontend.denoteCaps, hanon, hnames, hnP, List.map_nil, Frontend.denoteNList]
    | cons c rest =>
      rw [hc] at hcs
      obtain ⟨cP, restP, rfl, hcP, hrestP⟩ := mapM_option_cons_inv hcs
      obtain ⟨cvP, hcvP, rfl⟩ : ∃ cvP, Frontend.denoteCV st c.1 = some cvP ∧
          cP = (cvP, c.2) := by
        simp only [dCtor, Option.map_eq_some_iff] at hcP
        obtain ⟨x, hx, rfl⟩ := hcP
        exact ⟨x, hx, rfl⟩
      cases rest with
      | cons c' rest' =>
        obtain ⟨cP', restP', rfl, hcP', hrestP'⟩ := mapM_option_cons_inv hrestP
        have hall := dCtors_names hcs
        simp only [Frontend.denoteCaps, hanon, hnames, hnP, hall]
      | nil =>
        simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrestP
        subst hrestP
        simp only [Frontend.denoteCaps, hnames, hnP, denoteCV_name hcvP, Frontend.denoteNList]
        simp only [Option.some.injEq]
        generalize m.nIdx = a
        generalize c.2 = b
        cases a <;> cases b <;> cases isRec <;> rfl

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
    exact absurd hrun (fun h => AM.fail_ok h)
  | succ n ih =>
    intro e eP s₀ s' r hok hp hrun
    obtain ⟨hT, hd⟩ := hp
    simp only [Arena.piDomsMentionAny] at hrun
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [ite_eq_left htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨hs1, ho⟩ := viewBind_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some q =>
        obtain ⟨d, b⟩ := q
        have hw := view_forallE_of_viewBind htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨c, s₂, h3, h4⟩ := AM.bind_ok h2
        obtain ⟨p3, hc⟩ := mentionsAnyConst_spec names namesP d dP s₀ s₂ c hok ⟨hT, hdd⟩ h3
        simp only [RV] at hc
        subst hc
        by_cases hb : Expr.mentionsAnyConst namesP dP = true
        · rw [ite_eq_left hb] at h4
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
          exact ⟨p3, by simp [Expr.piDomsMentionAny, hb]⟩
        · rw [ite_eq_right hb] at h4
          obtain ⟨p4, h5⟩ := ih b bP s₂ s' r p3.ok
            ⟨denoteNListE_ext p3.ext _ _ hT, denote_ext hbd p3.ext⟩ h4
          refine ⟨p3.trans p4, ?_⟩
          simp only [RV] at h5
          simp [Expr.piDomsMentionAny, hb, h5]
    · rw [ite_eq_right htg] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨PStep.refl hok, ?_⟩
      show false = Expr.piDomsMentionAny namesP eP
      cases eP with
      | forallE d b => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons x xs ih =>
    intro ys s₀ s' r hok hp hrun
    obtain ⟨hq, hys⟩ := hp
    obtain ⟨y, ys', rfl, hy, hys'⟩ := mapM_option_cons_inv hys
    simp only [List.anyM] at hrun
    obtain ⟨b, s₁, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨p1, hb⟩ := hf x y s₀ s₁ b hok ⟨hq, hy⟩ h1
    simp only [RV] at hb
    subst hb
    cases hg : g y with
    | true =>
      rw [hg] at h2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨p1, by simp [hg]⟩
    | false =>
      rw [hg] at h2
      obtain ⟨p2, h3⟩ := ih ys' s₁ s' r p1.ok
        ⟨hQ p1.ext hq, hd.list p1.ext _ _ hys'⟩ h2
      exact ⟨p1.trans p2, by simp only [RV] at h3 ⊢; simp [hg, h3]⟩

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:90-102 blockIsRec
**Official's `is_rec`**, exactly: some member occurs in some binder domain
of the syntactic telescope of some declared constructor type. -/
theorem blockIsRec_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape) :
    PSpec (fun st => dShape st p = some pP) (Arena.blockIsRec p)
      (RV (ConLeche.blockIsRec pP)) := by
  intro s₀ s' r hok hp hrun
  have hnames := BlockShape.memberNames_spec hp
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv hp
  simp only [Arena.blockIsRec] at hrun
  have hQ : ∀ {st st' : EStore}, Ext st st' →
      Frontend.denoteNList st.ns p.memberNames = some pP.memberNames →
      Frontend.denoteNList st'.ns p.memberNames = some pP.memberNames :=
    fun hx h => denoteNListE_ext hx _ _ h
  have hin : ∀ (c : IConstantVal × Nat) (cP : ConstantVal × Nat),
      PSpec (fun st => Frontend.denoteNList st.ns p.memberNames = some pP.memberNames ∧
          dCtor st c = some cP)
        (Arena.piDomsMentionAny p.memberNames coreWalkFuel c.1.type)
        (RV (cP.1.type.piDomsMentionAny pP.memberNames)) := by
    intro c cP s₀ s' r hok hp hrun
    obtain ⟨hT, hc⟩ := hp
    simp only [dCtor, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc
    exact piDomsMentionAny_spec _ _ coreWalkFuel c.1.type cv.type s₀ s' r hok
      ⟨hT, denoteCV_type hcv⟩ hrun
  have hout : ∀ (m : Arena.MemberShape) (mP : ConLeche.MemberShape),
      PSpec (fun st => Frontend.denoteNList st.ns p.memberNames = some pP.memberNames ∧
          dMember st m = some mP)
        (m.ctors.anyM fun c => Arena.piDomsMentionAny p.memberNames coreWalkFuel c.1.type)
        (RV (mP.ctors.any fun c => c.1.type.piDomsMentionAny pP.memberNames)) := by
    intro m mP s₀ s' r hok hp hrun
    obtain ⟨hT, hm⟩ := hp
    obtain ⟨-, -, hcs, -⟩ := dMember_inv hm
    exact anyM_dpstep dCtor dCtor_ext _ hQ _ _ hin m.ctors mP.ctors s₀ s' r hok ⟨hT, hcs⟩ hrun
  exact anyM_dpstep dMember dMember_ext _ hQ _ _ hout p.members pP.members s₀ s' r hok
    ⟨hnames, hms⟩ hrun

/-! ## The formers and the constructors -/

/-- con-leche: ConLeche/Kernel/Install.lean:26-28 blockFormers — the indexed
form: the formers from position `k` on. -/
theorem blockFormers_go {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (isRec : Bool)
    (hcaps : ∀ i, Frontend.denoteCaps st (Arena.blockCapsAt p i isRec)
      = some (ConLeche.blockCapsAt pP i isRec)) :
    ∀ (ds : List IConstantVal) (dsP : List ConstantVal) (k : Nat),
      ds.mapM (Frontend.denoteCV st) = some dsP →
      Frontend.denoteCIList st ((ds.zipIdx k).map fun (cv, i) =>
          IConstantInfo.indInfo cv (Arena.blockCapsAt p i isRec))
        = some ((dsP.zipIdx k).map fun (cv, i) =>
          ConstantInfo.indInfo cv (ConLeche.blockCapsAt pP i isRec))
  | [], dsP, k, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    rfl
  | d :: ds, dsP, k, h => by
    obtain ⟨dP, dsP', rfl, hd, hds⟩ := mapM_option_cons_inv h
    simp only [List.zipIdx_cons, List.map_cons, Frontend.denoteCIList, Frontend.denoteCI, hd,
      hcaps, blockFormers_go isRec hcaps ds dsP' (k + 1) hds]

/-- con-leche: none — the members' declared formers denote. -/
theorem declared_denote {st : EStore} :
    ∀ {ms : List Arena.MemberShape} {msP : List ConLeche.MemberShape},
      ms.mapM (dMember st) = some msP →
      (ms.map (·.declared)).mapM (Frontend.denoteCV st) = some (msP.map (·.declared))
  | [], msP, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | m :: ms, msP, h => by
    obtain ⟨mP, msP', rfl, hm, hms⟩ := mapM_option_cons_inv h
    exact mapM_option_cons (dMember_inv hm).2.2.2 (declared_denote hms)

/-- con-leche: ConLeche/Kernel/Install.lean:26-28 blockFormers
**The formers**, in block order, as declared, with their capability records:
pure on both sides. -/
theorem blockFormers_denote {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (hanon : denoteN st.ns (default : NIdx) = some ConLeche.Name.anonymous)
    (hp : dShape st p = some pP) (isRec : Bool) :
    Frontend.denoteCIList st (Arena.blockFormers p isRec)
      = some (ConLeche.blockFormers pP isRec) := by
  obtain ⟨hms, -, -, -, -, -, -⟩ := dShape_inv hp
  exact blockFormers_go isRec (blockCapsAt_denote hanon hp · isRec) _ _ 0
    (declared_denote hms)

/-- con-leche: none — `dCtors`'s constructor list, read as constructor
records at `nP`. -/
theorem ctorInfos_denote {st : EStore} (nP : Nat) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)),
      dCtors st cs = some csP →
      Frontend.denoteCIList st (cs.map fun c => IConstantInfo.ctorInfo c.1 nP c.2)
        = some (csP.map fun c => ConstantInfo.ctorInfo c.1 nP c.2)
  | [], csP, h => by
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | c :: cs, csP, h => by
    obtain ⟨cP, csP', rfl, hc, hcs⟩ := mapM_option_cons_inv h
    simp only [dCtor, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc
    simp only [List.map_cons, Frontend.denoteCIList, Frontend.denoteCI, hcv, Option.map_some,
      ctorInfos_denote nP cs csP' hcs]

/-- con-leche: ConLeche/Kernel/Install.lean:30-32 blockCtors
**The constructors of every member**, as declared: pure on both sides. -/
theorem blockCtors_denote {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (hp : dShape st p = some pP) :
    Frontend.denoteCIList st (Arena.blockCtors p) = some (ConLeche.blockCtors pP) := by
  obtain ⟨-, -, hnP, -, -, -, -⟩ := dShape_inv hp
  simp only [Arena.blockCtors, ConLeche.blockCtors, hnP]
  exact ctorInfos_denote _ _ _ (BlockShape.allCtors_spec hp)

/-! ## The recursors -/

/-- con-leche: ConLeche/Kernel/Install.lean:34-37 Expr.dropVars
**`n` variables dropped**, each instantiated at `Sort 0`: the zero pin, the
sort interned, one `instantiate1` per variable. -/
theorem exprDropVars_run : ∀ (n : Nat) {s s' : AState} {e r : EIdx} {eP : Expr},
    StateOK s → PinsOK s → denoteE s.store e = some eP →
    Arena.exprDropVars n e s = .ok (r, s') →
    PStep s s' ∧ denoteE s'.store r = some (ConLeche.Expr.dropVars n eP)
  | 0, s, s', e, r, eP, hok, _, he, hrun => by
    simp only [Arena.exprDropVars] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, he⟩
  | n + 1, s, s', e, r, eP, hok, hpins, he, hrun => by
    simp only [Arena.exprDropVars] at hrun
    obtain ⟨z, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hz⟩ := zeroLevel_run hpins k1
    obtain ⟨s0, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hs0⟩ := internSortE_run hok hz k2
    obtain ⟨e', s₃, k3, z3⟩ := AM.bind_ok z2
    have he2 := denote_ext he p2.ext
    obtain ⟨q1, q2, q4, q5, -, q7⟩ := ExprOps.instantiate1Fast_run p2.ok hs0
      (by rw [he2]; rfl) k3
    have p3 : PStep s₂ s₃ := PStep.of_caches q1 q2 q4 q5
    have he3 : denoteE s₃.store e' = some (eP.instantiate1 (.sort .zero) 0) := q7 _ he2
    have p23 := p2.trans p3
    obtain ⟨p4, hr⟩ := exprDropVars_run n p23.ok (hpins.mono p23.ext p23.pins) he3 z3
    exact ⟨p23.trans p4, by simpa [ConLeche.Expr.dropVars] using hr⟩

/-- con-leche: ConLeche/Kernel/Install.lean:51 recFire (the parameters'
`map`) — `exprDropVars` over a list. -/
theorem dropVarsList_run (n : Nat) : ∀ (as : List EIdx) (asP : List Expr) {s s' : AState}
    {rs : List EIdx}, StateOK s → PinsOK s → Frontend.denoteEList s.store as = some asP →
    as.mapM (Arena.exprDropVars n) s = .ok (rs, s') →
    PStep s s' ∧ Frontend.denoteEList s'.store rs = some (asP.map (ConLeche.Expr.dropVars n))
  | [], asP, s, s', rs, hok, _, ha, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, rfl⟩
  | a :: as, asP, s, s', rs, hok, hpins, ha, hrun => by
    simp only [Frontend.denoteEList] at ha
    cases h1 : denoteE s.store a with
    | none => rw [h1] at ha; simp at ha
    | some x =>
    cases h2 : Frontend.denoteEList s.store as with
    | none => rw [h1, h2] at ha; simp at ha
    | some xs =>
    rw [h1, h2] at ha
    obtain rfl := (Option.some.inj ha).symm
    simp only [List.mapM_cons] at hrun
    obtain ⟨b, s₁, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨p1, hb⟩ := exprDropVars_run n hok hpins h1 k1
    obtain ⟨bs, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hbs⟩ := dropVarsList_run n as xs p1.ok (hpins.mono p1.ext p1.pins)
      (denoteEList_ext p1.ext _ _ h2) k2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨p1.trans p2, ?_⟩
    simp only [List.map_cons, Frontend.denoteEList, denote_ext hb p2.ext, hbs]

/-- con-leche: ConLeche/Kernel/Install.lean:39-54 recFire
**How a recursor's rules fire**, exactly: `.plain` at a member major and at
anything the major's domain does not read as a container; at an outside
container its levels and its parameters moved to the rule prefix. -/
theorem recFire_run {s s' : AState} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    {rc : Arena.RecShape} {rcP : ConLeche.RecShape} {f : IRecRuleFire}
    (hok : StateOK s) (hpins : PinsOK s) (hp : dShape s.store p = some pP)
    (hrc : dRec s.store rc = some rcP) (hrun : Arena.recFire p rc s = .ok (f, s')) :
    PStep s s' ∧ Frontend.denoteFire s'.store f = some (ConLeche.recFire pP rcP) := by
  have hk := BlockShape.k_spec hp
  obtain ⟨hcv, hrP, hmI, htgt, -, -⟩ := dRec_inv hrc
  unfold Arena.recFire at hrun
  by_cases ht : rc.tgt < p.k
  · rw [ite_eq_left ht] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨PStep.refl hok, ?_⟩
    simp only [ConLeche.recFire, show rcP.tgt < pP.k by rw [← htgt, ← hk]; exact ht, ite_true,
      Frontend.denoteFire]
  have ht' : ¬ rcP.tgt < pP.k := by rw [← htgt, ← hk]; exact ht
  rw [ite_eq_right ht] at hrun
  obtain ⟨o, s₁, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok (denoteCV_type hcv) k1
  rw [hmI] at hbp
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨PStep.refl hok, ?_⟩
    simp only [ConLeche.recFire, ht', ite_false, stripPis_none hbp, Frontend.denoteFire]
  | some q =>
  obtain ⟨bs, b⟩ := q
  obtain ⟨xs, x, hsp, -, hb⟩ := denoteBP_some hbp
  dsimp only at z1
  by_cases htg : (b.tag == ETag.forallE) = true
  · rw [ite_eq_left htg] at z1
    obtain ⟨o2, s₂, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨rfl, ho2⟩ := viewBind_run k2
    cases o2 with
    | none => exact absurd z2 (fun hc => failDanglingE_ok hc)
    | some q2 =>
    obtain ⟨dom, body⟩ := q2
    have hw := view_forallE_of_viewBind htg ho2.symm
    obtain ⟨domP, bodyP, rfl, hdom, -⟩ := denote_forallE_inv hok.wf hw hb
    dsimp only at z2
    obtain ⟨hd, s₃, k3, z3⟩ := AM.bind_ok z2
    obtain ⟨rfl, hhd⟩ := getAppFn_run hok hdom k3
    by_cases htc : (hd.tag == ETag.const) = true
    · rw [ite_eq_left htc] at z3
      obtain ⟨o4, s₄, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨rfl, ho4⟩ := viewConst_run k4
      cases o4 with
      | none => exact absurd z4 (fun hc => failDanglingE_ok hc)
      | some q4 =>
      obtain ⟨cn, us⟩ := q4
      have hvc := view_of_viewConst_tag htc ho4.symm
      obtain ⟨nm, ls, hgf, -, hus⟩ := denote_const_inv hok.wf hvc hhd
      dsimp only at z4
      obtain ⟨lvls, s₅, k5, z5⟩ := AM.bind_ok z4
      obtain ⟨rfl, hlv⟩ := viewLs_run k5
      have hls := hus
      simp only [denoteLs, hlv] at hls
      obtain ⟨args, s₆, k6, z6⟩ := AM.bind_ok z5
      obtain ⟨rfl, hargs⟩ := getAppArgs_run hok hdom k6
      have hlen : args.length = domP.getAppArgs.length :=
        (ExprOps.denoteEList_length _ _ hargs).symm
      obtain ⟨ps, s₇, k7, z7⟩ := AM.bind_ok z6
      obtain ⟨p7, hps⟩ := dropVarsList_run (rc.mI - rc.rP) _ _ hok hpins
        (denoteEList_take hargs (args.length - (rc.mI - rc.rP))) k7
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z7
      refine ⟨p7, ?_⟩
      have hls' : denoteLList s'.store.ls lvls = some ls := denoteLList_ext p7.ext.lss.ls _ _ hls
      simp only [ConLeche.recFire, ht', ite_false, hsp, hgf, Frontend.denoteFire,
        hls', hps, hlen, hmI, hrP]
    · rw [ite_eq_right htc] at z3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
      refine ⟨PStep.refl hok, ?_⟩
      have hnc : ∀ a b, domP.getAppFn ≠ .const a b := by
        intro a b h
        rw [h] at hhd
        exact htc (by rw [tag_const_of_denote hok.wf hhd]; rfl)
      -- the match's non-`const` arm, discharged off `hnc` in the context
      simp only [ConLeche.recFire, ht', ite_false, hsp, Frontend.denoteFire]
  · rw [ite_eq_right htg] at z1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨PStep.refl hok, ?_⟩
    simp only [ConLeche.recFire, ht', ite_false, hsp, Frontend.denoteFire]
    split
    · rename_i h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact absurd (tag_forallE_of_denote hok.wf hb) (by simpa using htg)
    · rfl

end ConRon.Bridge.Inductives
