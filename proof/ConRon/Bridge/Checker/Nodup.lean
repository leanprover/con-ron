/-
# `ConRon.Bridge.Checker.Nodup` — the pure checker keeps names unique

`Bridge/Checker/Split.lean`'s `checkDecl_nodup` (task #97-P3-Checker round 8's
child, closed in round 9): an accepted `ConLeche.checkDecl` step keeps the
environment's names pairwise distinct.  con-leche proves this for its CACHED
driver only (`Verify/Cached/PushChain.lean`'s `PushChain`, over `FEnv`); the
two-phase fold's bridge needs it for the PURE checker, which is what phase A's
`PhaseA` records.

The proof reads the run off con-leche's own run relation, `DeclRun`
(`checkDeclRun_ofEnvFactsK`), whose records already carry every duplicate
guard the checker ran:

| arm | the guard, in the run record |
|---|---|
| `defn` / `thm` / `opaque` / `axiom` | `ConstantValRun`'s first conjunct, `(env.find? cv.name).isNone` |
| `basis` (and a pinned `ind`/`quot` block) | `BasisInstallRun`'s per-constant `isNone` |
| `ind` (the uniform route, `DeclBlockRun`) | the formers' `checkConstantVal` (fresh at the base) and the front guard's `Nodup` of the member names; each constructor's `checkConstantVal` (fresh at the formers' environment, `checkSumCtors_names`) and the front guard's `Nodup` of the constructor names; the generated recursors fresh at the constructors' environment (`genRecCheck_out_fresh`) and pairwise distinct (`targetRecPins`' own `Nodup` test); `checkStructProjTable_inv`'s `projTableName` guard |

This module imports con-leche only: the statement and the proof are pure.
-/
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.EnvBound
import ConLeche.Verify.EnvWF
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.GenRecRun

namespace ConRon.Bridge

open ConLeche ConLeche.Semantics

set_option autoImplicit false

/-! ## Fresh pushes -/

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean PushChain.push — a push
of a name the environment does not hold keeps names unique. -/
theorem nodupNames_push {e : Env} {c : ConstantInfo} (hnd : NodupNames e)
    (hf : e.find? c.name = none) : NodupNames ⟨c :: e.consts⟩ := by
  unfold NodupNames at hnd ⊢
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨fun hmem => ?_, hnd⟩
  obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hmem
  have hne := List.find?_eq_none.mp hf x hx
  simp [hxn] at hne

theorem nodupNames_push' {e : Env} {c : ConstantInfo} (hnd : NodupNames e)
    (hf : (e.find? c.name).isNone = true) : NodupNames ⟨c :: e.consts⟩ :=
  nodupNames_push hnd (Option.isNone_iff_eq_none.mp hf)

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean FreshNames — a list of
names, pairwise distinct and each fresh at `e`. -/
def FreshAt (e : Env) (ns : List Name) : Prop :=
  ns.Nodup ∧ ∀ n ∈ ns, e.find? n = none

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean FreshNames.step — after
the head's push the tail is fresh at the extended environment. -/
theorem FreshAt.step {e : Env} {c : ConstantInfo} {ns : List Name}
    (h : FreshAt e (c.name :: ns)) : FreshAt ⟨c :: e.consts⟩ ns := by
  obtain ⟨hnd, hfr⟩ := h
  rw [List.nodup_cons] at hnd
  refine ⟨hnd.2, fun n hn => ?_⟩
  rw [Env.find?_cons, if_neg (fun he => hnd.1 (by rw [he]; exact hn))]
  exact hfr n (List.mem_cons_of_mem _ hn)

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean FreshNames.cons_of — fresh
at the extended environment, and the head fresh at the base, is fresh at the
base as a whole list. -/
theorem FreshAt.cons_of {e : Env} {c : ConstantInfo} {ns : List Name}
    (hc : e.find? c.name = none) (h : FreshAt ⟨c :: e.consts⟩ ns) :
    FreshAt e (c.name :: ns) := by
  obtain ⟨hnd, hfr⟩ := h
  have hne : ∀ n ∈ ns, c.name ≠ n ∧ e.find? n = none := by
    intro n hn
    have := hfr n hn
    rw [Env.find?_cons] at this
    by_cases he : c.name = n
    · rw [if_pos he] at this; exact nomatch this
    · rw [if_neg he] at this; exact ⟨he, this⟩
  refine ⟨List.nodup_cons.mpr ⟨fun hm => (hne _ hm).1 rfl, hnd⟩, ?_⟩
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact hc
  · exact (hne n hn).2

/-! ## The pinned blocks -/

/-- con-leche: ConLeche/Semantics/Decl.lean:57 BasisInstallRun — the pinned
block's install is a chain of fresh pushes. -/
theorem basisInstallRun_nodup : ∀ (cs : List ConstantInfo) {e e' : Env},
    BasisInstallRun e cs e' → NodupNames e → NodupNames e'
  | [], _, _, h, hnd => by
    simp only [BasisInstallRun] at h; subst h; exact hnd
  | c :: cs, e, e', h, hnd => by
    simp only [BasisInstallRun] at h
    exact basisInstallRun_nodup cs h.2 (nodupNames_push' hnd h.1)

theorem declBasisRun_nodup {e e' : Env} {k : BasisKind} (h : DeclBasisRun e k e')
    (hnd : NodupNames e) : NodupNames e' :=
  basisInstallRun_nodup _ h.2 hnd

/-! ## The uniform route -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:164 consSumCtors — the
constructors' conses push pairwise distinct names fresh at the base. -/
theorem consSumCtors_nodup (nP : Nat) : ∀ (cs : List (ConstantVal × Nat)) {e : Env},
    NodupNames e → FreshAt e (cs.map (·.1.name)) →
    NodupNames (consSumCtors nP cs e)
  | [], _, hnd, _ => hnd
  | c :: cs, e, hnd, hfr => by
    have hfr' : FreshAt e ((ConstantInfo.ctorInfo c.1 nP c.2).name :: cs.map (·.1.name)) :=
      hfr
    exact consSumCtors_nodup nP cs (nodupNames_push hnd (hfr.2 _ (List.mem_cons_self ..)))
      hfr'.step

/-- con-leche: ConLeche/Verify/Cached/AgreeFloor.lean consSumCtorsF_append — the
constructors' conses of an append are the two conses in turn (pure `Env`). -/
theorem consSumCtors_append (nP : Nat) :
    ∀ (a b : List (ConstantVal × Nat)) (e : Env),
      consSumCtors nP (a ++ b) e = consSumCtors nP b (consSumCtors nP a e)
  | [], _, _ => rfl
  | _ :: a, b, _ => consSumCtors_append nP a b _

/-- con-leche: ConLeche/Verify/Cached/AgreeFloor.lean:642 consBlockCtorsF_flatten —
the members' constructors, consed member by member, are the whole block's
constructors consed in block order (pure `Env`). -/
theorem consBlockCtors_flatten (nP : Nat) :
    ∀ (ctorsAs : List (List (ConstantVal × Nat))) (e : Env),
      consBlockCtors nP ctorsAs e = consSumCtors nP ctorsAs.flatten e
  | [], _ => rfl
  | ctorsA :: rest, e => by
    rw [consBlockCtors, List.flatten_cons, consSumCtors_append]
    exact consBlockCtors_flatten nP rest _

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean consBlockIndsF_push — the
formers' conses push pairwise distinct names fresh at the base. -/
theorem consBlockInds_nodup (p₁ : BlockShape) (isRec : Bool) :
    ∀ (cvTas : List ConstantVal) (i : Nat) {e : Env},
      NodupNames e → FreshAt e (cvTas.map (·.name)) →
      NodupNames (consBlockInds p₁ isRec cvTas i e)
  | [], _, _, hnd, _ => hnd
  | c :: cs, i, e, hnd, hfr => by
    have hfr' : FreshAt e
        ((ConstantInfo.indInfo c (blockCapsAt p₁ i isRec)).name :: cs.map (·.name)) := hfr
    exact consBlockInds_nodup p₁ isRec cs (i + 1)
      (nodupNames_push hnd (hfr.2 _ (List.mem_cons_self ..))) hfr'.step

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean consBlockRecsTF_push — the
recursors' conses at their majors push pairwise distinct names fresh at the
base. -/
theorem consBlockRecsT_nodup (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (q : BlockShape) :
    ∀ (out : List (ConstantVal × TargetMajor × List Expr)) (m : Nat) {e : Env},
      NodupNames e → FreshAt e (out.map (·.1.name)) →
      NodupNames (consBlockRecsT find? resolves q m out e)
  | [], _, _, hnd, _ => hnd
  | (cv, M, rhss) :: rest, m, e, hnd, hfr => by
    have hfr' : FreshAt e
        ((ConstantInfo.recInfo cv (q.majorIdxAt m) (q.rulePrefixAt m)
          (tgtStoredRules find? resolves cv (q.majorIdxAt m) (q.rulePrefixAt m) M rhss)).name
          :: rest.map (·.1.name)) := hfr
    exact consBlockRecsT_nodup find? resolves q rest (m + 1)
      (nodupNames_push hnd (hfr.2 _ (List.mem_cons_self ..))) hfr'.step

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean checkBlockTablesF_push — every
projection table's push is guarded by its own lookup. -/
theorem checkBlockTables_nodup (p : BlockShape) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) {e e' : Env},
      checkBlockTables (m := CheckM) p l e = .ok e' → NodupNames e → NodupNames e'
  | [], e, e', h, hnd => by
    simp only [checkBlockTables, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hnd
  | (ms, ctorsA, sortss) :: rest, e, e', h, hnd => by
    unfold checkBlockTables at h
    obtain ⟨e'', hstep, hrest⟩ := exceptBind_ok h
    refine checkBlockTables_nodup p rest hrest ?_
    split at hstep
    · split at hstep
      · obtain ⟨-, -, -, -, hfP, rfl⟩ := checkStructProjTable_inv hstep
        exact nodupNames_push hnd hfP
      · simp only [pure, Except.pure, Except.ok.injEq] at hstep
        subst hstep; exact hnd
    · simp only [pure, Except.pure, Except.ok.injEq] at hstep
      subst hstep; exact hnd

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:120 checkBlockTeles —
the members' formers carry the members' names, each fresh at the base. -/
theorem checkBlockTeles_names {mode : CheckMode} {F : Nat} {env : Env} {nP : Nat} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      checkBlockTeles (fueledOps mode F) env nP mss = .ok cvs →
      cvs.map (·.1.name) = mss.map (·.cvT.name) ∧ ∀ q ∈ cvs, env.find? q.1.name = none
  | [], cvs, h => by
    simp only [checkBlockTeles, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, fun _ h => nomatch h⟩
  | ms :: rest, cvs, h => by
    unfold checkBlockTeles at h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    obtain ⟨qs, hqs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨ih1, ih2⟩ := checkBlockTeles_names hqs
    obtain ⟨cvTa, s⟩ := q
    obtain ⟨cvT, hn, -, hccv, -⟩ := checkBlockTele_shape hq
    obtain ⟨hf, -, -, -, -, -, ty, -, -, -, -, -, -, -, heq⟩ := checkConstantVal_inv hccv
    have hname : cvTa.name = cvT.name := by rw [heq]
    refine ⟨by simp only [List.map_cons, ih1, hname, hn], ?_⟩
    intro q hq'
    rcases List.mem_cons.mp hq' with rfl | hq'
    · show env.find? cvTa.name = none
      rw [hname]; exact hf
    · exact ih2 q hq'

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:152 checkSumCtors — the
annotated constructors carry the declared names, each fresh at the
constructors' environment. -/
theorem checkSumCtors_names {mode : CheckMode} {F : Nat} {env₀ env : Env} {T : Name}
    {lps : List Name} {nP nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {cvTa : ConstantVal} {cs ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (h : checkSumCtors (fueledOps mode F) env₀ env T lps nP nIdx resSort isProp large
      cvTa cs = .ok (ctorsA, sortss)) :
    ctorsA.map (·.1.name) = cs.map (·.1.name) ∧ ∀ c ∈ ctorsA, env.find? c.1.name = none := by
  obtain ⟨hlen, -, hall⟩ := checkSumCtors_inv h
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem (by simp [hlen])
    intro j h1 h2
    have hj1 : j < ctorsA.length := by simpa using h1
    have hj2 : j < cs.length := by simpa using h2
    simp only [List.getElem_map]
    obtain ⟨-, sorts, -, hrun⟩ := hall j _ _ (List.getElem?_eq_getElem hj2)
      (List.getElem?_eq_getElem hj1)
    obtain ⟨⟨ty', hccvC⟩, -⟩ := checkSumCtor_shape hrun
    obtain ⟨-, -, -, -, -, -, ty, -, -, -, -, -, -, -, heq⟩ := checkConstantVal_inv hccvC
    rw [heq]
  · intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < cs.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    obtain ⟨-, sorts, -, hrun⟩ := hall j _ _ (List.getElem?_eq_getElem hj') hj
    obtain ⟨⟨ty', hccvC⟩, -⟩ := checkSumCtor_shape hrun
    obtain ⟨hf, -, -, -, -, -, ty, -, -, -, -, -, -, -, heq⟩ := checkConstantVal_inv hccvC
    rw [heq]; exact hf

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:488 targetRecPins — the
pins check the family's names pairwise distinct. -/
theorem targetRecPins_nodup {q : BlockShape} {block : List ConstantInfo}
    (h : targetRecPins (m := CheckM) q block = .ok ()) : (q.recs.map (·.cvR.name)).Nodup := by
  by_cases hn : (q.recs.map (·.cvR.name)).Nodup
  · exact hn
  exfalso
  unfold targetRecPins at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  simp only [hn, ↓reduceIte] at h
  repeat' split at h
  all_goals exact nomatch h

/-- con-leche: ConLeche/Verify/Inductives/GenRecRun.lean:910 genRecCheck_out_fresh —
the stored family carries the records' names, in order. -/
theorem genRecCheck_out_names {mode : CheckMode} {env : Env} {p : BlockShape}
    {nestedBit : Bool} {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead}
    {Ms₀ : List TargetMajor} {cvTas : List ConstantVal} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) (mkFEnv env) p nestedBit params tbl rd Ms₀ cvTas
      block = .ok out) :
    out.map (·.1.name) = p.recs.map (·.cvR.name) := by
  obtain ⟨R⟩ := genRecCheck_run h
  have hcvGs := R.hcvGs
  have hrules := R.hrules
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run hrules
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map]
  cases hi : p.recs[i]? with
  | none =>
    have : out[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hi ⊢
      have : out.length ≤ R.cvGs.length := by rw [hlenO]; exact Nat.min_le_left _ _
      omega
    simp [this]
  | some rc =>
    obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG i rc hi
    obtain ⟨rhss, hoi, -⟩ := hallO i cvG c hG hc
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcv⟩ := classConstOk_inv T.hcv
    simp only [hoi, Option.map_some]
    rw [hcv]

/-- con-leche: ConLeche/Semantics/Inductives/DeclBlock.lean:40 DeclBlockRun —
the uniform install pushes the formers, the constructors, the recursors and
the projection tables, each at a name found fresh. -/
theorem declBlockRun_nodup {μ : CheckMode} {F : Nat} {e e' : Env}
    {block : List ConstantInfo} {p₀ : BlockParts} (h : DeclBlockRun μ F e block p₀ e')
    (hnd : NodupNames e) : NodupNames e' := by
  obtain ⟨hndC, hndM, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, ctx, holes, rd, Ms, kinds,
    nfs, pos, st, isorts, out, hInd, hp, hCtors, -, -, -, -, -, -, hRec, hTbl⟩ := h
  -- the formers: the members' names, each fresh at the base
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, hcv, hp1, henv1, htele0, hteles, -⟩ :=
    checkBlockInds_shape hInd
  obtain ⟨cvT0, hn0, -, hccv0, -⟩ := checkBlockTele_shape htele0
  obtain ⟨hf0, -, -, -, -, -, ty0, -, -, -, -, -, -, -, heq0⟩ := checkConstantVal_inv hccv0
  have hname0 : cvTa0.name = ms0.cvT.name := by rw [heq0]; exact hn0
  obtain ⟨hnsR, hfrR⟩ := checkBlockTeles_names hteles
  have hnamesT : cvTas.map (·.name) = p₀.members.map (·.cvT.name) := by
    rw [hcv, hm, List.map_cons, List.map_cons, hname0, List.map_map, ← hnsR]
    rfl
  have hnd1 : NodupNames env₁ := by
    rw [henv1]
    refine consBlockInds_nodup p₁ isRec cvTas 0 hnd ⟨?_, ?_⟩
    · rw [hnamesT]; exact hndM
    · intro n hn
      rw [hcv] at hn
      rcases List.mem_cons.mp hn with rfl | hn
      · show e.find? cvTa0.name = none
        rw [hname0, ← hn0]; exact hf0
      · rw [List.map_map] at hn
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hn
        exact hfrR q hq
  -- the constructors: the block's by name, each fresh at the formers' environment
  have hmem : p.members = p₀.members := by
    rw [hp, BlockParts.complete_members, hp1, BlockShape.withSort_members]
  have hlenT : cvTas.length = p.members.length := by
    have := congrArg List.length hnamesT
    simp only [List.length_map] at this
    rw [this, hmem]
  obtain ⟨hlenC, -, hallC⟩ := checkBlockCtors_inv hCtors
  have hper : ∀ (i : Nat) (hi : i < p.members.length), ∃ ctorsA, ctorsAs[i]? = some ctorsA ∧
      ctorsA.map (·.1.name) = p.members[i].ctors.map (·.1.name) ∧
      ∀ c ∈ ctorsA, env₁.find? c.1.name = none := by
    intro i hi
    have hz : (p.members.zip cvTas)[i]? = some (p.members[i], cvTas[i]) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨ctorsA, sortss, hcA, -, hrun⟩ := hallC i _ hz
    obtain ⟨h1, h2⟩ := checkSumCtors_names hrun
    exact ⟨ctorsA, hcA, h1, h2⟩
  have hlenC' : ctorsAs.length = p.members.length := by
    rw [hlenC, List.length_zip, hlenT, Nat.min_self]
  have hnamesC : ctorsAs.flatten.map (·.1.name) = p₀.allCtors.map (·.1.name) := by
    have : ctorsAs.map (List.map (·.1.name))
        = p.members.map (fun ms => ms.ctors.map (·.1.name)) := by
      apply List.ext_getElem (by simp [hlenC'])
      intro i h1 h2
      have hi : i < p.members.length := by simpa using h2
      obtain ⟨ctorsA, hcA, hn, -⟩ := hper i hi
      simp only [List.getElem_map]
      obtain ⟨_, hh⟩ := List.getElem?_eq_some_iff.mp hcA
      rw [hh, hn]
    rw [List.map_flatten, this, BlockShape.allCtors, List.map_flatten, List.map_map, ← hmem]
    rfl
  have hfrC : ∀ c ∈ ctorsAs.flatten, env₁.find? c.1.name = none := by
    intro c hc
    obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcs
    have hi' : i < p.members.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    obtain ⟨ctorsA, hcA, -, hfr⟩ := hper i hi'
    rw [hi] at hcA
    obtain rfl := Option.some.inj hcA
    exact hfr c hc
  have hnd2 : NodupNames (consBlockCtors p.nP ctorsAs env₁) := by
    rw [consBlockCtors_flatten]
    refine consSumCtors_nodup p.nP _ hnd1 ⟨by rw [hnamesC]; exact hndC, ?_⟩
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    exact hfrC c hc
  -- the recursors: fresh at the constructors' environment, distinct by the pins
  obtain ⟨R⟩ := checkBlockRec_run hRec
  have hnd3 := consBlockRecsT_nodup (consBlockCtors p.nP ctorsAs env₁).find?
    (·.constsResolve (consBlockCtors p.nP ctorsAs env₁)) p.toBlockShape out 0 hnd2
    ⟨by rw [genRecCheck_out_names hRec]; exact targetRecPins_nodup R.pins, fun n hn => by
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hn
      exact genRecCheck_out_fresh hRec o ho⟩
  -- the tables
  exact checkBlockTables_nodup _ _ hTbl hnd3

/-! ## The whole step -/

/-- con-leche: ConLeche/Verify/Cached/InstalledC.lean installRun_trace — **the
pure fold keeps names unique**: every install is guarded by a `find?` miss
(`checkConstantVal`, `installBasisDecl`, the inductive install), which is
what con-leche's `PushChain` carries through its cached fold.  Read off
`DeclRun` arm by arm (the module note). -/
theorem checkDecl_nodup {μ : CheckMode} {pinsP : List NatOpPinSet} {F : Nat}
    {env env' : Env} {d : Declaration}
    (h : ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env')
    (hnd : NodupNames env) : NodupNames env' := by
  have hrun := checkDeclRun_ofEnvFactsK h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, -, rfl, -⟩ := hrun
    exact nodupNames_push' hnd hcv.1
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact nodupNames_push' hnd hcv.1
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl, -⟩ := hrun
    exact nodupNames_push' hnd hcv.1
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, hdisj⟩
    · exact hnd
    · rcases hdisj with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
      · exact nodupNames_push' hnd hcv.1
      · exact nodupNames_push' hnd hcv.1
      · exact nodupNames_push' hnd hcv.1
      · exact hnd
  | basisDecl kind => exact declBasisRun_nodup hrun hnd
  | quotDecl k cv =>
    cases k with
    | type => exact declBasisRun_nodup hrun hnd
    | _ => (simp only [DeclRun] at hrun; subst hrun; exact hnd)
  | indDecl block nP =>
    simp only [DeclRun] at hrun
    split at hrun
    · exact declBasisRun_nodup hrun hnd
    · simp only [DeclIndRunDispatchK] at hrun
      split at hrun
      · exact declBlockRun_nodup hrun hnd
      · exact hrun.elim

end ConRon.Bridge
