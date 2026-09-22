/-
# `ConRon.Bridge.Inductives.SumInstall` — Theorem 1 for the direct install's stages

`Arena/Inductives/SumInstall.lean`'s seventeen twins against
`ConLeche/Kernel/Inductives/SumInstall.lean` (and the eight `…F` `abbrev`s of
`SumInstallF.lean`, which are the same functions — task #97d-2's deviation 1).
These are the stages the fixpoint route runs: the former's telescope, the
capability record, the per-field universe bound, the positivity
normalisation, the constructors' stage and the generated rules.

**Mostly CORE grade.**  `whnfTelescope` calls `whnf`, `checkStructFieldSortsI`
calls `inferTypeCore` and `ensureSort`, `normPosDom` calls `whnf`,
`normCtorVal` and `checkSumCtor` call all of them — so their frame is
`CoreStep` and their hypothesis is `CoreSpec`.  Four are pure grade
(`closeTelescope`, `zipFvarDoms`, `consSumCtors`, the two arithmetic readers).

## Two of task #97d-2's five removed higher-order arguments are here

* `checkSumInd`'s `capsOf : InductiveShape → IndCaps` became `isRec : Bool`,
  with `nativeCapsAt` moved one module earlier.  The statement compares the
  twin with con-leche at `capsOf := fun p => ConLeche.nativeCapsAt p isRec`,
  which is that deviation written down.
* `sumRules`' `find? : Name → Option ConstantInfo` became `fe : IFEnv`.  The
  statement compares it at `find? := env.find?`, which is what `IFEnvOK`'s
  `hit`/`cover` pair says the index is.
-/
import ConRon.Bridge.Inductives.StructInstall

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The two arithmetic readers

`InductiveShape.rulePrefix` and `.majorIdx` read only `Nat` fields and the
constructor list's LENGTH, so they are equal on the nose once the shape
relation holds — the tier's second pair of closed results.
`denoteCtors_length` itself MOVED to `Bridge/Inductives/Rel.lean` in round 5:
`NativeParts.lean`'s `nativeRecPinOk_spec` is below this file in the import
chain and needs it. -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:292-294 InductiveShape.rulePrefix
The recursor's rule prefix `nP + 1 + n`. -/
theorem rulePrefix_spec {st : EStore} {p : Arena.InductiveShape}
    {q : ConLeche.InductiveShape} (h : ShapeRel st p q) :
    p.rulePrefix = q.rulePrefix := by
  simp only [Arena.InductiveShape.rulePrefix, ConLeche.InductiveShape.rulePrefix,
    h.nP, denoteCtors_length _ _ h.ctors]

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:295 InductiveShape.majorIdx
The major premise's index. -/
theorem majorIdx_spec {st : EStore} {p : Arena.InductiveShape}
    {q : ConLeche.InductiveShape} (h : ShapeRel st p q) :
    p.majorIdx = q.majorIdx := by
  simp only [Arena.InductiveShape.majorIdx, ConLeche.InductiveShape.majorIdx,
    rulePrefix_spec h, h.nIdx]

/-! ## The former's telescope -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:45-68 whnfTelescope
Peel `n` Π binders, reducing at each step, down to the result `Sort`.

`sorry`: a `Nat` recursion over `CoreSpec.knot`'s `whnf` slot and
`Bridge/Rel.lean`'s `forallE`/`sort` inversions. -/
theorem whnfTelescope_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (i n : Nat) (e : EIdx) (eP : Expr) :
    CSpec μ env fe
      (fun st => denoteE st e = some eP ∧ denoteFEnv st fe = some env)
      (Arena.whnfTelescope μ fe i n e)
      (fun st r => ∃ F bsP sP,
        ConLeche.whnfTelescope (ConLeche.fueledOps μ F) env i n eP
          = .ok (bsP, sP) ∧
        denoteBinders st r.1 = some bsP ∧ denoteL st.ls r.2 = some sP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:70-78 closeTelescope
Close a body under a telescope, abstracting the free variables as it goes.
PURE grade: `abstract1Fast` and `internE`, no knot.

`sorry`: a list induction over `Bridge/ExprOps/Abs.lean`'s
`abstract1Fast_spec` and `internE_spec` at `.forallE`. -/
theorem closeTelescope_spec (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (i : Nat) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => denoteBinders st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.closeTelescope bs i body)
      (RE (ConLeche.closeTelescope bsP i bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:80-94 checkSumTele
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
The type former's stage: the telescope checked and the result sort measured.

`sorry`: `whnfTelescope_spec` and `closeTelescope_spec`, plus `CoreSpec.knot`'s
`defeq` slot for the stored type's comparison. -/
theorem checkSumTele_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (cv : IConstantVal) (cvP : ConstantVal)
    (n : Nat) (cvTa₀ : IConstantVal) (cvTa₀P : ConstantVal) :
    CSpec μ env fe
      (fun st => Frontend.denoteCV st cv = some cvP ∧
        Frontend.denoteCV st cvTa₀ = some cvTa₀P ∧
        denoteFEnv st fe = some env)
      (Arena.checkSumTele μ fe cv n cvTa₀)
      (fun st r => ∃ F cvAP sP,
        ConLeche.checkSumTele (ConLeche.fueledOps μ F) env cvP n cvTa₀P
          = .ok (cvAP, sP) ∧
        Frontend.denoteCV st r.1 = some cvAP ∧ denoteL st.ls r.2 = some sP) := by
  sorry

/-! ## The capability record -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
The capability record the block's shape licenses — eta at a non-`Prop`
structure-like block, unit-likeness at a fieldless constructor, rule K at
official's `is_K_target`.  Twinned in `SumInstall.lean` rather than
`NativeInstall.lean` (task #97d-2's deviation 3: `checkSumInd`'s `capsOf`
became `isRec`, which moves this one module earlier).

**STATEMENT DEFECT, round 4 — and it is NOT confined to this statement.**
The `_` arm of both sides answers the DEFAULT capability record, and the two
defaults do not correspond: `Arena/Env.lean`'s `IIndCaps.etaCtor` defaults to
`(default : NIdx)`, the zero word, while `ConLeche.IndCaps.etaCtor` defaults
to `.anonymous` — and `Arena/Env.lean`'s own comment on that field says so
outright ("con-leche's default is `.anonymous`; the handle's is the zero word.
Neither is a name the field ever *denotes*").  `Frontend.denoteCaps` READS
`etaCtor` unconditionally, so `RCaps (ConLeche.nativeCapsAt q isRec)` at a
block with zero or two-or-more constructors asks for

    denoteN st.ns (default : NIdx) = some ConLeche.Name.anonymous

and **no invariant of this library says that**.  `StateOK` does not; `PinsOK`
does not (its six clauses are the forty-nine pin slots, the reserved list and
the three nullary values).  The zero word is tag `NTag.anonymous = 0`, tier
`tierP`, index 0, so it decodes exactly when the persistent name store's
`anons` table is non-empty — true in every state the checker actually reaches,
and provable from nothing that is currently stated.

**Why this is bigger than one `sorry`.**  `checkSumInd` pushes
`.indInfo cvTa caps` with exactly this record, so at every MULTI-CONSTRUCTOR
inductive the fixpoint route installs, `Frontend.denoteCI` of the new row —
and therefore `denoteFEnv` of the new index, and therefore `InstRel`'s
`denote` clause and `FoldOK.denote` above it — is `none` unless the zero name
handle decodes.  This is a hole in the DENOTATION layer, not in this tier's
statement layer, and it wants a decision one level up: either the pin
invariant gains the clause (`denoteN s.store.ns default = some .anonymous`,
which `internAllPins` establishes and which is one lemma once stated), or
`Frontend.denoteCaps` stops reading `etaCtor` where `eta = false` — the same
"the denotation should forget the representation's extra data" argument that
settled `.projInfo`'s `tableName` in round 3, but here the forgetting is
conditional and that is a Frontend-tier call.

Left `sorry` rather than proved at a weakened statement: the singleton arm
goes through today (the shape relation's fields, `readLevel_spec` — the twin
does NOT call `lvlEq?`, so `PSpec` is the right grade — and `denoteCV_name` at
the constructor handle), and it is the `_` arm alone that is stuck.  The same
hole blocks `nativeCaps_spec` (`Bridge/Inductives/NativeInstall.lean`), which
is this statement at `p.toInductiveShape`. -/
theorem nativeCapsAt_spec (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (isRec : Bool) :
    PSpec (fun st => ShapeRel st p q)
      (Arena.nativeCapsAt p isRec) (RCaps (ConLeche.nativeCapsAt q isRec)) := by
  sorry

/-! ## The former's install stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:96-112 checkSumInd
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-43 checkSumIndF
The type former checked and installed, and the shape record completed with the
sort its telescope measured.  **Deviation 3's `capsOf`** is instantiated here.

`sorry`: `checkSumTele_spec`, `withSort_spec` (`Bridge/Inductives/SumParts.lean`),
`nativeCapsAt_spec`, and `IFEnv.push`'s two lemmas for the `InstRel`. -/
theorem checkSumInd_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (isRec : Bool) :
    CSpec μ env fe
      (fun st => ShapeRel st p q ∧ denoteFEnv st fe = some env)
      (Arena.checkSumInd μ fe p isRec)
      (fun st r => ∃ F envP cvTaP qP,
        ConLeche.checkSumInd (ConLeche.fueledOps μ F) env q
            (fun x => ConLeche.nativeCapsAt x isRec) = .ok (envP, cvTaP, qP) ∧
        InstRel fe (fun e => e = envP) st r.1 ∧
        Frontend.denoteCV st r.2.1 = some cvTaP ∧ ShapeRel st r.2.2 qP) := by
  sorry

/-! ## The fields' universe bound -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:114-139 checkStructFieldSortsI
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:45-61 checkStructFieldSortsIF
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:63-81 checkStructFieldSortsIFA
Each field's sort, checked against the family's — official's
subsingleton-elimination criterion at a one-constructor block.

`sorry`: a `Nat` recursion over `CoreSpec.knot`'s `infer` slot,
`CoreSpec.sort`'s `EnsureSortSpec`, and `Bridge/ExprOps/Leaves.lean`'s
`fvarTypeD`. -/
theorem checkStructFieldSortsI_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (isProp large : Bool) (s : LIdx)
    (sP : Level) (nP : Nat) (fvs idxArgs : List EIdx)
    (fvsP idxArgsP : List Expr) (j : Nat) :
    CSpec μ env fe
      (fun st => denoteL st.ls s = some sP ∧
        Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st idxArgs = some idxArgsP ∧
        denoteFEnv st fe = some env)
      (Arena.checkStructFieldSortsI μ fe isProp large s nP fvs idxArgs j)
      (fun st r => ∃ F ls,
        ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp
          large sP nP fvsP idxArgsP j = .ok ls ∧
        denoteLList st.ls r = some ls) := by
  sorry

/-! ## The positivity normalisation -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:141-175 normPosDom
Reduce a field domain until it no longer mentions the block, or give up.

`sorry`: a fuel induction over `CoreSpec.knot`'s `whnf` slot and
`mentionsConst_spec`. -/
theorem normPosDom_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (d fuel : Nat) (e : EIdx) (eP : Expr) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧ denoteE st e = some eP ∧
        denoteFEnv st fe = some env)
      (Arena.normPosDom μ fe T d fuel e)
      (fun st r => ∃ F v,
        ConLeche.normPosDom (ConLeche.fueledOps μ F) env TP d fuel eP = .ok v ∧
        denoteE st r = some v) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:177-188 normFieldDoms
The constructor's field domains, each normalised, opened at free variables.

`sorry`: a `Nat` recursion over `normPosDom_spec` and
`Bridge/ExprOps/Subst.lean`'s `instantiate1Fast_spec`. -/
theorem normFieldDoms_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (i n : Nat) (h : EIdx) (hP : Expr) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP ∧
        denoteFEnv st fe = some env)
      (Arena.normFieldDoms μ fe T i n h)
      (fun st r => ∃ F bsP rP,
        ConLeche.normFieldDoms (ConLeche.fueledOps μ F) env TP i n hP
          = .ok (bsP, rP) ∧
        denoteBinders st r.1 = some bsP ∧ denoteE st r.2 = some rP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
`zipFvarDoms` is task #97d-2's replacement for con-leche's `zipWith` inside
`normCtorVal`: it reads each free variable's own type off the store, which is
what makes the normalised domains the ones the walk opened.

**PROVED** (task #97-P3-Ind round 4): the list induction over `fvarTypeD_run`
(`Bridge/Inductives/Rel.lean`, off `Bridge/ExprOps/Spine.lean`'s closed
`fvarTypeD_spec`).  `fvarTypeD` is read-only, so the whole zip is one
`PStep.refl`. -/
theorem zipFvarDoms_spec (xs : List EIdx) (xsP : List Expr)
    (bs : List (EIdx × BinderMeta)) (bsP : List (Expr × BinderMeta)) :
    PSpec (fun st => Frontend.denoteEList st xs = some xsP ∧
        denoteBinders st bs = some bsP)
      (Arena.zipFvarDoms xs bs)
      (fun st r => ∃ ts, denoteBinders st r = some ts ∧
        ts.length = min xsP.length bsP.length) := by
  induction xs generalizing xsP bs bsP with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hx, hb⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [Arena.zipFvarDoms] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], rfl, by simp⟩
  | cons x xs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hx, hb⟩ := hpre
    cases bs with
    | nil =>
      simp only [denoteBinders, Option.some.injEq] at hb
      subst hb
      simp only [Arena.zipFvarDoms] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨PStep.refl hok, [], rfl, by simp⟩
    | cons b bs =>
      obtain ⟨bt, bm⟩ := b
      simp only [Frontend.denoteEList] at hx
      cases hx1 : denoteE s₀.store x with
      | none => rw [hx1] at hx; simp at hx
      | some xP =>
        cases hxs : Frontend.denoteEList s₀.store xs with
        | none => rw [hx1, hxs] at hx; simp at hx
        | some xsP' =>
          rw [hx1, hxs] at hx
          obtain rfl := Option.some.inj hx
          simp only [denoteBinders] at hb
          cases hb1 : denoteE s₀.store bt with
          | none => rw [hb1] at hb; simp at hb
          | some btP =>
            cases hbs : denoteBinders s₀.store bs with
            | none => rw [hb1, hbs] at hb; simp at hb
            | some bsP' =>
              rw [hb1, hbs] at hb
              obtain rfl := Option.some.inj hb
              simp only [Arena.zipFvarDoms] at hrun
              obtain ⟨t, s₁, h1, h2⟩ := bindOk hrun
              obtain ⟨rfl, ht⟩ := fvarTypeD_run hok hx1 h1
              obtain ⟨rest, s₂, h3, h4⟩ := bindOk h2
              obtain ⟨hstep, ts, hts, hlen⟩ :=
                ih xsP' bs bsP' _ s₂ rest hok ⟨hxs, hbs⟩ h3
              obtain ⟨rfl, rfl⟩ := pureOk h4
              refine ⟨hstep, (xP.fvarTypeD, bm) :: ts, ?_, ?_⟩
              · simp only [denoteBinders, denote_ext ht hstep.ext, hts]
              · simp only [List.length_cons, hlen]
                omega

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:83-95 normCtorValF
The constructor's stored type rebuilt from the normalised domains.

`sorry`: `normFieldDoms_spec`, `zipFvarDoms_spec` and `closeTelescope_spec`. -/
theorem normCtorVal_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (nP nF : Nat) (cvC cvCa : IConstantVal) (cvCP cvCaP : ConstantVal) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteCV st cvC = some cvCP ∧
        Frontend.denoteCV st cvCa = some cvCaP ∧
        denoteFEnv st fe = some env)
      (Arena.normCtorVal μ fe T nP nF cvC cvCa)
      (fun st r => ∃ F v,
        ConLeche.normCtorVal (ConLeche.fueledOps μ F) env TP nP nF cvCP cvCaP
          = .ok v ∧ Frontend.denoteCV st r = some v) := by
  sorry

/-! ## The constructors' stage -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
One constructor checked: its telescope, its parameter domains, its residual,
its field sorts and its normalised stored value.

`sorry`: `checkSumTele_spec`, `checkStructDomsAt_spec`
(`Bridge/Inductives/StructInstall.lean`), `checkStructFieldSortsI_spec`,
`normCtorVal_spec` and `structCtorResidOk_spec`. -/
theorem checkSumCtor_spec {μ : CheckMode} {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvC : IConstantVal) (cvCP : ConstantVal) (nF : Nat)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvC = some cvCP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkSumCtor μ fe₀ fe T lps nP nIdx resSort isProp large cvC nF cvTa)
      (fun st r => ∃ F cvCaP sortsP,
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvCP nF cvTaP = .ok (cvCaP, sortsP) ∧
        Frontend.denoteCV st r.1 = some cvCaP ∧
        denoteLList st.ls r.2 = some sortsP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:255-267 checkSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:130-140 checkSumCtorsF
The whole constructor list.

`sorry`: a list induction over `checkSumCtor_spec`. -/
theorem checkSumCtors_spec {μ : CheckMode} {env : Env} (fe₀ fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (resSort : LIdx) (resSortP : Level) (isProp large : Bool)
    (cvTa : IConstantVal) (cvTaP : ConstantVal) (env₀ : Env)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls resSort = some resSortP ∧
        Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st cs = some csP ∧
        denoteFEnv st fe₀ = some env₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkSumCtors μ fe₀ fe T lps nP nIdx resSort isProp large cvTa cs)
      (fun st r => ∃ F ctorsAP sortssP,
        ConLeche.checkSumCtors (ConLeche.fueledOps μ F) env₀ env TP lpsP nP
          nIdx resSortP isProp large cvTaP csP = .ok (ctorsAP, sortssP) ∧
        denoteCtors st r.1 = some ctorsAP ∧
        denoteLLists st r.2 = some sortssP) := by
  sorry

/-! ## The constructors consed, and the rules -/

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:269-272 consSumCtors
con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:142-145 consSumCtorsF
The constructors pushed into the index.  PURE on both sides.

`sorry`: a list induction over `IFEnv.push`'s `denoteFEnv` clause; the
`IFEnvCoh` and `Pushed` halves are `push`'s own two lemmas. -/
theorem consSumCtors_spec (st : EStore) (nP : Nat)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (fe : IFEnv) (env : Env) (hcs : denoteCtors st cs = some csP)
    (hfe : denoteFEnv st fe = some env) (hcoh : IFEnvCoh fe) :
    InstRel fe (fun e => e = ConLeche.consSumCtors nP csP env) st
      (Arena.consSumCtors nP cs fe) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:274-290 sumRules
The recursor's rules, one per constructor, with their firing bits.  **Task
#97d-2's deviation 3 again**: con-leche takes `find? : Name → Option
ConstantInfo` and the twin takes the index `fe`, so the statement compares
them at `find? := env.find?` — which is what `IFEnvOK` says the index is.

`sorry`: `Bridge/ExprOps/TelescopeF.lean`'s `recRulePlain_spec` (closed) and
`Arena/Env.lean`'s `recRuleBits` against con-leche's, whose nested case needs
`nestedRuleShape`. -/
theorem sumRules_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (recName : NIdx) (recNameP : ConLeche.Name) (nP mI rP : Nat)
    (recTy : EIdx) (recTyP : Expr) (cs : List (IConstantVal × Nat))
    (csP : List (ConstantVal × Nat)) (rhss : List EIdx) (rhssP : List Expr) :
    CSpec μ env fe
      (fun st => denoteN st.ns recName = some recNameP ∧
        denoteE st recTy = some recTyP ∧ denoteCtors st cs = some csP ∧
        Frontend.denoteEList st rhss = some rhssP ∧
        denoteFEnv st fe = some env)
      (Arena.sumRules fe recName nP mI rP recTy cs rhss)
      (fun st r => Frontend.denoteRules st r
        = some (ConLeche.sumRules env.find? recNameP nP mI rP recTyP csP rhssP)) := by
  sorry

end ConRon.Bridge.Inductives
