/-
# `ConRon.Bridge.Checker.Nodup` — the pure checker keeps names unique

`Bridge/Checker/Split.lean`'s `checkDecl_nodup` (task #97-P3-Checker round 8's
child, closed in round 9): an accepted `ConLeche.checkDecl` step keeps the
environment's names pairwise distinct.  con-leche proves this for its CACHED
driver only (`Verify/Cached/PushChain.lean`'s `PushChain`, over `FEnv`); the
two-phase fold's bridge needs it for the PURE checker, which is what phase A's
`PhaseA` records.

The proof reads the run off con-leche's own run relation, `DeclRun`
(`checkDeclRun_ofEnvFactsE`), whose records already carry every duplicate
guard the checker ran:

| arm | the guard, in the run record |
|---|---|
| `defn` / `thm` / `opaque` / `axiom` | `ConstantValRun`'s first conjunct, `(env.find? cv.name).isNone` |
| `basis` (and a pinned `ind`/`quot` block) | `BasisInstallRun`'s per-constant `isNone` |
| `ind`, modeled | `MemberValRun` per member and per provisioned recursor (the provisional environment holds the recursors before it, so the group is pairwise distinct), `ProjFnRun`'s `projFnName` guard |
| `ind`, native | `checkConstantVal_inv` at the former, each constructor (`checkSumCtors_inv`) and the recursor, the front guard's `Nodup` of the constructor names, and `checkStructProjTable_inv`'s `projTableName` guard |

This module imports con-leche only: the statement and the proof are pure.
-/
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Verify.Inductives.FixInv
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.EnvBound
import ConLeche.Verify.EnvWF

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

/-! ## The modeled route -/

/-- con-leche: ConLeche/Semantics/DeclIndRun.lean:83 IndMembersRun — the
member fold pushes each member at a name its front door found fresh. -/
theorem indMembersRun_nodup {μ : CheckMode} {F : Nat} {bn : List Name}
    {caps : IndCaps} : ∀ (cs : List ConstantInfo) {e e' : Env},
      IndMembersRun μ F bn caps e cs e' → NodupNames e → NodupNames e'
  | [], _, _, h, hnd => by
    simp only [IndMembersRun] at h; subst h; exact hnd
  | ci :: cs, e, e', h, hnd => by
    simp only [IndMembersRun] at h
    obtain ⟨cvA, ⟨type', hcv, rfl, -⟩, h⟩ := h
    have hf := hcv.1
    cases ci with
    | indInfo v caps' => exact indMembersRun_nodup cs h (nodupNames_push' hnd hf)
    | ctorInfo v nP nF => exact indMembersRun_nodup cs h (nodupNames_push' hnd hf)
    | _ => exact h.elim

/-- con-leche: ConLeche/Semantics/DeclIndRun.lean:99 ProvisionRecsRun — the
provisioned recursor group's names are pairwise distinct and fresh at the
base: each was checked fresh at the provisional environment holding the ones
before it. -/
theorem provisionRecsRun_fresh {μ : CheckMode} {F : Nat} {bn : List Name} :
    ∀ (cs : List ConstantInfo) {e eS : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsRun μ F bn e cs eS checked →
      FreshAt e (checked.map (·.1.name))
  | [], _, _, _, h => by
    simp only [ProvisionRecsRun] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | ci :: cs, e, eS, checked, h => by
    simp only [ProvisionRecsRun] at h
    obtain ⟨cvA, mI, rP, rules, rest', -, ⟨type', hcv, rfl, -⟩, hrest, rfl⟩ := h
    have hf : e.find? ci.toConstantVal.name = none :=
      Option.isNone_iff_eq_none.mp hcv.1
    have ih := provisionRecsRun_fresh cs hrest
    exact FreshAt.cons_of
      (c := .recInfo ⟨ci.toConstantVal.name, ci.toConstantVal.levelParams, type'⟩ mI rP [])
      hf ih

/-- con-leche: ConLeche/Semantics/DeclIndRun.lean:273 IndRecsRun.IndRecsFoldRun —
the group's install fold pushes the provisioned names in order. -/
theorem indRecsFoldRun_nodup {μ : CheckMode} {F : Nat} {bn : List Name}
    {eB eS : Env} : ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      {acc out : Env},
      IndRecsRun.IndRecsFoldRun μ F bn eB eS acc checked out →
      NodupNames acc → FreshAt acc (checked.map (·.1.name)) → NodupNames out
  | [], _, _, h, hnd, _ => by
    simp only [IndRecsRun.IndRecsFoldRun] at h; subst h; exact hnd
  | c :: cs, acc, out, h, hnd, hfr => by
    simp only [IndRecsRun.IndRecsFoldRun] at h
    obtain ⟨rules', -, h⟩ := h
    have hfr' : FreshAt acc
        ((ConstantInfo.recInfo c.1 c.2.1 c.2.2.1 rules').name :: cs.map (·.1.name)) := hfr
    exact indRecsFoldRun_nodup cs h
      (nodupNames_push hnd (hfr.2 _ (List.mem_cons_self ..))) hfr'.step

theorem indRecsRun_nodup {μ : CheckMode} {F : Nat} {bn : List Name}
    {e e' : Env} {recs : List ConstantInfo}
    (h : IndRecsRun μ F bn e recs e') (hnd : NodupNames e) : NodupNames e' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, eS, checked, hprov, hfold⟩
  · exact hnd
  · exact indRecsFoldRun_nodup checked hfold hnd (provisionRecsRun_fresh recs hprov)

/-- con-leche: ConLeche/Semantics/DeclIndRun.lean:376 ProjInstallRun — each
projection function is pushed at a name its guard found fresh. -/
theorem projInstallRun_nodup {μ : CheckMode} {F : Nat} {T C : Name}
    {lps : List Name} {nP nF : Nat} : ∀ (is : List Nat) {e e' : Env},
      ProjInstallRun μ F T C lps nP nF e is e' → NodupNames e → NodupNames e'
  | [], _, _, h, hnd => by
    simp only [ProjInstallRun] at h; subst h; exact hnd
  | i :: is, e, e', h, hnd => by
    simp only [ProjInstallRun] at h
    obtain ⟨e'', hstep, hrest⟩ := h
    refine projInstallRun_nodup is hrest ?_
    rcases hstep with ⟨cvj, mcv, mval, mhint, pty, rhsA, -, -, -, hf, hrun⟩ | ⟨-, rfl⟩
    · have heq := hrun.2.2.2.2.2.2.2.2.2.2.2.2
      rw [heq]
      exact nodupNames_push' hnd hf
    · exact hnd

theorem declIndRun_nodup {μ : CheckMode} {F : Nat} {e e' : Env}
    {block : List ConstantInfo} (h : DeclIndRun μ F e block e')
    (hnd : NodupNames e) : NodupNames e' := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨cvT, capsT, cvC, nP, nF, -, -, envM, envR, hM, hR, -, -, hP⟩ |
    ⟨-, envM, hM, hR⟩
  · exact projInstallRun_nodup _ hP (indRecsRun_nodup hR (indMembersRun_nodup _ hM hnd))
  · exact indRecsRun_nodup hR (indMembersRun_nodup _ hM hnd)

/-! ## The native route -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:270 consSumCtors — the
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

theorem declNativeRun_nodup {μ : CheckMode} {F : Nat} {e e' : Env}
    {p₀ : NativeParts} (h : DeclNativeRun μ F e p₀ e') (hnd : NodupNames e) :
    NodupNames e' := by
  obtain ⟨hndC, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, tfvs, trest,
    isorts, hInd, hp, hCtors, -, -, -, -, -, -, -, hRec, hTbl⟩ := h
  -- the former
  obtain ⟨cvT, s, -, -, hccv, hp1, henv1, -⟩ := checkSumInd_shape hInd
  obtain ⟨hfT, -, -, -, -, -, ty, -, -, -, -, -, -, -, heqT⟩ := checkConstantVal_inv hccv
  have hnd1 : NodupNames env₁ := by
    rw [henv1]
    exact nodupNames_push hnd (by show e.find? cvTa.name = none; rw [heqT]; exact hfT)
  -- the constructors: the block's by name, each fresh at the former's environment
  have hctors : p.ctors = p₀.ctors := by
    rw [hp, hp1]; rfl
  obtain ⟨hlen, -, hall⟩ := checkSumCtors_inv hCtors
  have hnames : ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) := by
    rw [← hctors]
    apply List.ext_getElem (by simp [hlen])
    intro j h1 h2
    have hj1 : j < ctorsA.length := by simpa using h1
    have hj2 : j < p.ctors.length := by simpa using h2
    simp only [List.getElem_map]
    have hc : p.ctors[j]? = some (p.ctors[j]'hj2) := List.getElem?_eq_getElem hj2
    have hcA : ctorsA[j]? = some (ctorsA[j]'hj1) := List.getElem?_eq_getElem hj1
    obtain ⟨-, sorts, -, hrun⟩ := hall j _ _ hc hcA
    obtain ⟨⟨ty', hccvC⟩, -⟩ := checkSumCtor_shape hrun
    obtain ⟨-, -, -, -, -, -, ty, -, -, -, -, -, -, -, heq⟩ := checkConstantVal_inv hccvC
    rw [heq]
  have hfresh : ∀ c ∈ ctorsA, env₁.find? c.1.name = none := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    obtain ⟨-, sorts, -, hrun⟩ := hall j _ _ (List.getElem?_eq_getElem hj') hj
    obtain ⟨⟨ty', hccvC⟩, -⟩ := checkSumCtor_shape hrun
    obtain ⟨hf, -, -, -, -, -, ty, -, -, -, -, -, -, -, heq⟩ := checkConstantVal_inv hccvC
    rw [heq]; exact hf
  have hnd2 : NodupNames (consSumCtors p.nP ctorsA env₁) :=
    consSumCtors_nodup p.nP ctorsA hnd1 ⟨by rw [hnames]; exact hndC, fun n hn => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      exact hfresh c hc⟩
  -- the recursor
  obtain ⟨cvRi, recTy, -, -, hccvR, -, -, -, -, -, -, -, -, -, rfl⟩ := checkNativeRec_shape hRec
  obtain ⟨hfR, -⟩ := checkConstantVal_inv hccvR
  have hnd3 := nodupNames_push (c := .recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
    p.majorIdx p.rulePrefix
    (sumRules (consSumCtors p.nP ctorsA env₁).find? p.cvR.name p.nP p.majorIdx
      p.rulePrefix recTy ctorsA rhss)) hnd2 hfR
  -- the projection table
  unfold checkNativeTable at hTbl
  split at hTbl
  · split at hTbl
    · obtain ⟨bodies, -, -, -, hfP, rfl⟩ := checkStructProjTable_inv hTbl
      exact nodupNames_push hnd3 hfP
    · simp only [pure, Except.pure, Except.ok.injEq] at hTbl
      subst hTbl; exact hnd3
  · simp only [pure, Except.pure, Except.ok.injEq] at hTbl
    subst hTbl; exact hnd3

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
  have hrun := checkDeclRun_ofEnvFactsE h
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
    · simp only [DeclIndRunDispatch] at hrun
      split at hrun
      · exact declNativeRun_nodup hrun hnd
      · exact declIndRun_nodup hrun hnd

end ConRon.Bridge
