/-
# `ConRon.Bridge.Checker.Pushes` — what the pure checker's step pushes

Two facts about con-leche's KERNEL step `ConLeche.checkDecl`
(`ConLeche/Kernel/CheckDecl.lean`) at the fueled operations, the ones the
stream index's view needs:

* `checkDecl_pushes` — an accepted step returns the environment with the
  declaration's constants and tables pushed, `env.pushDelta (declConstants d)
  (declTables d)` (`ConLeche/Kernel/Install.lean`): a function of the
  declaration alone;
* `checkDecl_fresh` — those constants' names are pairwise distinct and none of
  them is in `env`.

con-leche proves both for its CACHED step (`checkDeclStepC_pushes`,
`Verify/Cached/DeclPushes.lean`; `checkDeclStepC_push`/`PushChain`,
`Verify/Cached/PushChain.lean`); these are the same statements for the kernel
step.  Both are read off con-leche's run relation `DeclRun`
(`checkDeclRun_ofEnvFactsK`, `Semantics/Bridge/Sound.lean`), whose records
carry every arm's result environment and every duplicate guard the checker ran:

| arm | result | the guard, in the run record |
|---|---|---|
| `defn` / `thm` / `opaque` / `axiom` | one cons | `ConstantValRun`'s first conjunct, `(env.find? cv.name).isNone` |
| `Quot.sound` axiom, `quot` | one cons | `DeclQuotRun`'s `isNone` |
| `sorryAx` | `env` | none needed |
| `ind` block `readBlock` reads (`BlockRun`), a pinned basis block included | `checkBlock`'s final `pushDelta` | below |

A block `readBlock` reads installs `blockConstants p₀`: the formers, then the
constructors, then the recursors (`blockConstants_names`).  `BlockRun` runs its
stages at the REDUCED members `ms`, whose declared formers, names and
constructors are `p₀`'s (`reduceMembers_inv`).  The formers are fresh at `env`
(each member's `checkBlockTele` runs `checkConstantVal` at `env`) and distinct
(the block's own `memberNames.Nodup` guard); the constructors are fresh at the
formers' environment (`BlockCtorsRun`'s per-constructor `checkConstantVal`) and
distinct (the block's `allCtors` guard); the recursors are fresh at the
constructors' environment (`genRecCheck_out_fresh`, at the names
`genRecCheck_out_names`) and distinct (`targetRecPins`' own `Nodup` test).
Fresh at a later environment means fresh at `env` and none of the earlier
stages' names (`find?_none_append`).

The freshness half is con-leche's `Cached.FreshAt`, used as is.
-/
module

public import ConLeche.Kernel.CheckDecl
public import ConLeche.Kernel.Install
public import ConLeche.Semantics.Bridge.Sound
public import ConLeche.Verify.Extend.Inversions
public import ConLeche.Verify.ExceptBind
public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Verify.Inductives.BlockInv
public import ConLeche.Verify.Inductives.BlockShapeInv
public import ConLeche.Verify.Cached.PushChain
public import ConLeche.Verify.Cached.BlockPushes
public import ConLeche.Semantics.Inductives.DeclBlock

public section

namespace ConRon.Bridge

open ConLeche ConLeche.Semantics
open ConLeche.Cached (blockConstants_names)

set_option autoImplicit false

/-! ## Lookups past a push -/

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean FreshNames — a list of
names, pairwise distinct and each fresh at `e` (upstream's is not exposed). -/
@[expose] def FreshAt (e : Env) (ns : List Name) : Prop :=
  ns.Nodup ∧ ∀ n ∈ ns, e.find? n = none

/-- con-leche: ConLeche/Kernel/Env.lean:467 Env.find? — a name an environment
with `X` pushed does not hold is none of `X`'s and not in the environment
below. -/
theorem find?_none_append {X : List ConstantInfo} {e : Env} {t : List ProjTable} {n : Name}
    (h : (⟨X ++ e.consts, t⟩ : Env).find? n = none) :
    n ∉ X.map (·.name) ∧ e.find? n = none := by
  unfold Env.find? at h ⊢
  rw [List.find?_append] at h
  cases hX : X.find? (·.name == n) with
  | some x => rw [hX] at h; exact nomatch h
  | none =>
    rw [hX, Option.none_or] at h
    refine ⟨fun hm => ?_, h⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    have := List.find?_eq_none.mp hX x hx
    simp at this

/-- `find?_none_append` at a list pushed oldest first (`Env.pushDelta`'s
order). -/
theorem find?_none_append_rev {X : List ConstantInfo} {e : Env} {t : List ProjTable} {n : Name}
    (h : (⟨X.reverse ++ e.consts, t⟩ : Env).find? n = none) :
    n ∉ X.map (·.name) ∧ e.find? n = none := by
  obtain ⟨h₁, h₂⟩ := find?_none_append h
  refine ⟨fun hm => h₁ ?_, h₂⟩
  rw [List.map_reverse, List.mem_reverse]
  exact hm

/-- One constant fresh at `e`: a fresh singleton. -/
theorem fresh_one {e : Env} {c : ConstantInfo} (h : e.find? c.name = none) :
    FreshAt e ([c].map (·.name)) :=
  ⟨by simp, fun n hn => by
    rw [List.map_cons, List.map_nil, List.mem_singleton] at hn
    rw [hn]; exact h⟩

/-! ## The blocks `readBlock` reads -/

/-- con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:154 checkBlock — **an
accepted block pushes its constants and tables**: the install is the check's
final `pure`. -/
theorem checkBlock_pushes {ops : CheckerOps CheckM} {env env' : Env}
    {block : List ConstantInfo} {p₀ : BlockShape}
    (h : checkBlock ops env block p₀ = .ok env') :
    env' = env.pushDelta (blockConstants p₀) ((blockTables p₀ p₀.members).getD []) := by
  unfold checkBlock at h
  cases ht : blockTables p₀ p₀.members with
  | none =>
    simp only [ht, unwrapOr, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at h
    repeat' split at h
    all_goals contradiction
  | some Q =>
    simp only [ht, unwrapOr, bind, Except.bind, pure, Except.pure, Option.getD_some] at h ⊢
    repeat' split at h
    all_goals try contradiction
    all_goals exact (Except.ok.inj h).symm

/-- con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:120 checkBlockTeles —
every member's former was checked fresh at the base. -/
theorem checkBlockTeles_fresh {mode : CheckMode} {F : Nat} {env : Env} {nP : Nat} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      checkBlockTeles (fueledOps mode F) env nP mss = .ok cvs →
      ∀ ms ∈ mss, env.find? ms.cvT.name = none
  | [], _, _ => fun _ h => nomatch h
  | ms :: rest, cvs, h => by
    unfold checkBlockTeles at h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    obtain ⟨qs, hqs, -⟩ := exceptBind_ok h
    obtain ⟨cvT, hn, -, -, hccv, -⟩ := checkBlockTele_shape hq
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rw [← hn]; exact (checkConstantVal_inv hccv).1
    · exact checkBlockTeles_fresh hqs m hm

/-- con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:496 targetRecPins — the
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

/-- con-leche: ConLeche/Verify/Inductives/GenRecRun.lean:744 genRecCheck_run —
the generated family carries the records' names, in order. -/
theorem genRecCheck_out_names {mode : CheckMode} {fe : FEnv} {p : BlockShape}
    {nestedBit : Bool} {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead}
    {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (fueledOps mode F) fe p nestedBit params tbl rd Ms₀
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
    simp only [hoi, Option.map_some]
    rw [T.hcvG]

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean blockConstants_names (its
formers clause) — the formers' conses push the declared formers' names. -/
theorem consBlockInds_names (p₁ : BlockShape) (isRec : Bool) :
    ∀ (l : List ConstantVal) (i : Nat),
      ((l.zipIdx i).map fun x => ConstantInfo.indInfo x.1 (blockCapsAt p₁ x.2 isRec)).map
        (·.name) = l.map (·.name)
  | [], _ => rfl
  | a :: l, i => by
    simp only [List.zipIdx_cons, List.map_cons]
    exact congrArg (a.name :: ·) (consBlockInds_names p₁ isRec l (i + 1))

/-- con-leche: ConLeche/Semantics/Inductives/DeclBlock.lean BlockRun — **a
recognised block's constants are fresh**: the formers at the base, the
constructors at the formers' environment, the recursors at the constructors',
each stage's names distinct (the module note). -/
theorem blockRun_fresh {F : Nat} {env env' : Env} {block : List ConstantInfo}
    {p₀ : BlockShape} (hd : ∀ m ∈ p₀.members, m.declared = m.cvT)
    (h : BlockRun F env block p₀ env') :
    FreshAt env ((blockConstants p₀).map (·.name)) := by
  obtain ⟨ms, hms, hAt, -, hndC, hndM, -, isRec, env₁, p₁, sortsss, ctx, holes, rd, Ms,
    kinds, nfs, pos, st, isorts, out, -, hInd, hCtors, -, -, -, -, -, -, hRec, -, -, -, -, -⟩ := h
  obtain ⟨-, hdecl, -, -, hctors⟩ := reduceMembers_inv hd hms
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, hp1, henv1, htele0, hteles, -⟩ :=
    checkBlockInds_shape hInd
  subst hp1
  -- the members' names: declared, at the reduced members, in `p₀`
  have hNM : p₀.members.map (·.declared.name) = ms.map (·.cvT.name) := by
    have e₁ : p₀.members.map (·.declared.name) = (p₀.members.map (·.declared)).map (·.name) := by
      rw [List.map_map]; rfl
    have e₂ : ms.map (·.declared.name) = (ms.map (·.declared)).map (·.name) := by
      rw [List.map_map]; rfl
    rw [e₁, ← hdecl, ← e₂]
    exact List.map_congr_left fun m hm => (hAt m hm).name.symm
  have hNC : p₀.allCtors = ms.flatMap (·.ctors) := by
    show (p₀.members.map (·.ctors)).flatten = _
    rw [← hctors, List.flatMap_def]
  -- the formers: fresh at the base
  have hfrM : ∀ m ∈ ms, env.find? m.cvT.name = none := by
    intro m hm'
    change ms = ms0 :: rest at hm
    rw [hm] at hm'
    rcases List.mem_cons.mp hm' with rfl | hm'
    · obtain ⟨cvT, hn, -, -, hccv, -⟩ := checkBlockTele_shape htele0
      rw [← hn]; exact (checkConstantVal_inv hccv).1
    · exact checkBlockTeles_fresh hteles m hm'
  -- what the formers' environment does not hold
  have hE₁ : ∀ n, env₁.find? n = none → n ∉ ms.map (·.cvT.name) ∧ env.find? n = none := by
    intro n hn
    rw [henv1, consBlockInds_consts'] at hn
    obtain ⟨h₁, h₂⟩ := find?_none_append_rev hn
    refine ⟨fun hm' => h₁ ?_, h₂⟩
    rw [consBlockInds_names]
    have : (({ p₀ with members := ms } : BlockShape).members.map (·.declared)).map (·.name)
        = p₀.members.map (·.declared.name) := by
      show (ms.map (·.declared)).map (·.name) = _
      rw [hdecl, List.map_map]; rfl
    rw [this, hNM]; exact hm'
  -- the constructors: fresh at the formers' environment
  have hfrC : ∀ c ∈ p₀.allCtors, env₁.find? c.1.name = none := by
    intro c hc
    rw [hNC, List.mem_flatMap] at hc
    obtain ⟨m, hm', hc⟩ := hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hm'
    obtain ⟨sortss, -, -, -, hall⟩ := hCtors.2 i m hi
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨-, -, -, ⟨-, hccv⟩, -⟩ := hall j c c hj hj
    exact (checkConstantVal_inv hccv).1
  -- what the constructors' environment does not hold
  have hE₂ : ∀ n, (consBlockCtors ({ p₀ with members := ms } : BlockShape).nP
      (({ p₀ with members := ms } : BlockShape).withSort s0).memberCtors env₁).find? n = none →
      n ∉ p₀.allCtors.map (·.1.name) ∧ env₁.find? n = none := by
    intro n hn
    rw [consBlockCtors_eq] at hn
    obtain ⟨h₁, h₂⟩ := find?_none_append_rev hn
    refine ⟨fun hm' => h₁ ?_, h₂⟩
    rw [List.map_map]
    have : (({ p₀ with members := ms } : BlockShape).withSort s0).memberCtors.flatten
        = p₀.allCtors := by
      show (ms.map (·.ctors)).flatten = _
      rw [hNC, List.flatMap_def]
    rw [this]
    exact hm'
  -- the recursors: fresh at the constructors' environment, distinct by the pins
  unfold checkBlockRec at hRec
  obtain ⟨R⟩ := genRecCheck_run hRec
  have hndR : (p₀.recs.map (·.cvR.name)).Nodup := by have := targetRecPins_nodup R.pins; exact this
  have hnamesR := genRecCheck_out_names hRec
  have hfrR : ∀ rc ∈ p₀.recs, (consBlockCtors ({ p₀ with members := ms } : BlockShape).nP
      (({ p₀ with members := ms } : BlockShape).withSort s0).memberCtors env₁).find?
        rc.cvR.name = none := by
    intro rc hrc
    have : rc.cvR.name ∈ out.map (·.1.name) := by
      rw [hnamesR]; exact List.mem_map_of_mem hrc
    obtain ⟨o, ho, hon⟩ := List.mem_map.mp this
    rw [← hon]
    exact genRecCheck_out_fresh hRec o ho
  -- assemble
  have hndM' : (ms.map (·.cvT.name)).Nodup := hndM
  have hndC' : (p₀.allCtors.map (·.1.name)).Nodup := by
    have : ({ p₀ with members := ms } : BlockShape).allCtors = p₀.allCtors := by
      show (ms.map (·.ctors)).flatten = _
      rw [hNC, List.flatMap_def]
    rw [← this]; exact hndC
  rw [blockConstants_names, hNM]
  refine ⟨?_, fun n hn => ?_⟩
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hndM', hndC', fun a ha b hb => ?_⟩, hndR, fun a ha b hb => ?_⟩
    · rintro rfl
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact (hE₁ _ (hfrC c hc)).1 ha
    · rintro rfl
      obtain ⟨rc, hrc, hn⟩ := List.mem_map.mp hb
      have hf := hfrR rc hrc
      rw [hn] at hf
      obtain ⟨h₃, h₄⟩ := hE₂ _ hf
      rcases List.mem_append.mp ha with ha | ha
      · exact (hE₁ _ h₄).1 ha
      · exact h₃ ha
  · rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp hn with hn | hn
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hn
        exact hfrM m hm'
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        exact (hE₁ _ (hfrC c hc)).2
    · obtain ⟨rc, hrc, rfl⟩ := List.mem_map.mp hn
      exact (hE₁ _ (hE₂ _ (hfrR rc hrc)).2).2

/-! ## The value arms -/

/-- con-leche: ConLeche/Semantics/DeclRun.lean ConstantValRun — the stored
type is the declared one, and the name was fresh. -/
theorem constantValRun_type {F : Nat} {env : Env} {cv : ConstantVal} {type' : Expr}
    (h : ConstantValRun F env cv type') : type' = cv.type ∧ env.find? cv.name = none :=
  ⟨h.2.2.2.2.1, Option.isNone_iff_eq_none.mp h.1⟩

/-- con-leche: ConLeche/Kernel/StdAxioms.lean:185 stdAxiomOk — the tolerated
axiom is no standard one (cf. `Cached.tolerated_not_std`). -/
theorem stdAxiomOk_sorry {env : Env} {cv : ConstantVal} (ht : cv.name = sorryAxName) :
    stdAxiomOk env cv = false := by
  rw [stdAxiomOk, ite_eq_right, ite_eq_right] <;> rw [ht] <;> decide

/-! ## The whole step -/

/-- The run record, both halves at once. -/
theorem checkDecl_pushes_fresh {pinsP : List NatOpPinSet} {F : Nat} {env env' : Env}
    {d : Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env d = .ok env') :
    env' = env.pushDelta (declConstants d) (declTables d) ∧
      FreshAt env ((declConstants d).map (·.name)) := by
  obtain ⟨-, hrun⟩ := checkDeclRun_ofEnvFactsK h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvf, rfl, -, -⟩ := hrun
    obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
    obtain rfl : value' = value := hvf.2.2.1
    exact ⟨rfl, fresh_one hfr⟩
  | thmDecl cv value =>
    obtain ⟨-, type', value', hcv, -, -, rfl⟩ := hrun
    obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
    exact ⟨rfl, fresh_one hfr⟩
  | opaqueDecl cv value =>
    obtain ⟨-, type', value', hcv, -, rfl, -⟩ := hrun
    obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
    exact ⟨rfl, fresh_one hfr⟩
  | axiomDecl cv =>
    rcases hrun with ⟨hq, -, -, hfr, rfl⟩ | ⟨hqs, type', -, hcv, hdisj⟩
    · simp only [declConstants, declTables, ite_eq_left hq]
      exact ⟨rfl, fresh_one (Option.isNone_iff_eq_none.mp hfr)⟩
    · obtain ⟨rfl, hfr⟩ := constantValRun_type hcv
      dsimp only at hdisj
      simp only [declConstants, declTables, ite_eq_right hqs]
      rcases hdisj with ⟨hstd, rfl⟩ | ⟨hn, -, rfl⟩ | ⟨hn, -, rfl⟩ |
          ⟨-, -, -, -, -, -, hs, rfl⟩
      · have hs : cv.name ≠ sorryAxName := fun he => by
          have : stdAxiomOk env cv = true := hstd
          rw [stdAxiomOk_sorry he] at this
          exact nomatch this
        rw [ite_eq_right hs]
        exact ⟨rfl, fresh_one hfr⟩
      · have hs : cv.name ≠ sorryAxName := by rw [hn]; decide
        rw [ite_eq_right hs]
        exact ⟨rfl, fresh_one hfr⟩
      · have hs : cv.name ≠ sorryAxName := by rcases hn with hn | hn <;> rw [hn] <;> decide
        rw [ite_eq_right hs]
        exact ⟨rfl, fresh_one hfr⟩
      · rw [ite_eq_left hs]
        exact ⟨rfl, List.nodup_nil, fun _ h => nomatch h⟩
  | quotDecl k cv =>
    obtain ⟨-, -, hfr, rfl⟩ := hrun
    exact ⟨rfl, fresh_one (Option.isNone_iff_eq_none.mp hfr)⟩
  | indDecl block nP =>
    simp only [DeclKindRun, DeclIndRunDispatchK] at hrun
    obtain ⟨hK, -⟩ := ConLeche.checkDecl_inv h
    simp only [ConLeche.checkDeclKind] at hK
    cases hbp : readBlock nP block with
    | error e => simp only [hbp] at hrun
    | ok p =>
      simp only [hbp] at hrun
      simp only [declConstants, declTables, hbp]
      by_cases hok : indParamsOk nP block = true
      · rw [ite_eq_left hok, hbp] at hK
        exact ⟨checkBlock_pushes hK, blockRun_fresh (readBlock_declared hbp) hrun⟩
      · rw [ite_eq_right hok] at hK
        exact nomatch hK

/-- con-leche: ConLeche/Verify/Cached/DeclPushes.lean checkDeclStepC_pushes —
**an accepted kernel step pushes what its declaration installs**: the result
environment is a function of the declaration (the module note). -/
theorem checkDecl_pushes {pinsP : List NatOpPinSet} {F : Nat} {env env' : Env} {d : Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env d = .ok env') :
    env' = env.pushDelta (declConstants d) (declTables d) :=
  (checkDecl_pushes_fresh h).1

/-- con-leche: ConLeche/Verify/Cached/PushChain.lean checkDeclStepC_push —
**what an accepted kernel step pushes is fresh**: its names pairwise distinct
and none of them in the environment it ran at (the module note). -/
theorem checkDecl_fresh {pinsP : List NatOpPinSet} {F : Nat} {env env' : Env} {d : Declaration}
    (h : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env d = .ok env') :
    ((declConstants d).map (·.name)).Nodup ∧ ∀ c ∈ declConstants d, env.find? c.name = none := by
  obtain ⟨-, hnd, hfr⟩ := checkDecl_pushes_fresh h
  exact ⟨hnd, fun c hc => hfr _ (List.mem_map_of_mem hc)⟩

end ConRon.Bridge
