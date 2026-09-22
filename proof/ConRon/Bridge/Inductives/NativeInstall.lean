/-
# `ConRon.Bridge.Inductives.NativeInstall` — Theorem 1 for the fixpoint route

`Arena/Inductives/NativeInstall.lean`'s seventeen twins against
`ConLeche/Kernel/Inductives/NativeInstall.lean` (and `NativeInstallF.lean`'s
five `abbrev`s, which are the same five functions).  This is the route
`nativeParts?` recognises: the two-pass install of a direct recursive block.

## `NativePass` is not generic, and what that costs the statement

con-leche parameterises `NativePass` by the environment representation (`Env`
at the pure install, `FEnv` at its cached driver's mirror); the arena has ONE
(task #97d-2's deviation 9), so the twin's record is `NativePass` flat and the
relation below compares it with `ConLeche.NativePass Env`.  Nothing else about
the two records differs.

## The capability record's verdict, and why the statement has a `Bool` beside it

Task #268's `checkNativePass` runs at a syntactic reading of `is_rec` and
answers whether the classification CONFIRMS it; `checkNative` re-runs the pass
once if it does not.  The `Bool` is therefore part of the answer relation, and
the route theorem's two branches are the two values it can take.
-/
import ConRon.Bridge.Inductives.SumInstall

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The free-variable memo -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:143-148 MentionsFvarMemoInv
The handle-keyed memo of `mentionsFvar q`. -/
def FvarMemoOK (q : Nat) (tbl : Std.HashMap EIdx Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k = some e ∧ r = Expr.mentionsFvar q e

/-! ## The three pure readers off the record -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
Is any field recursive or reflexive?  A `Bool` off the kinds alone, so the
twin's and con-leche's agree under `kindOf` — and this one is CLOSED. -/
theorem nativeIsRec_spec (kinds : List (List Arena.RecFieldKind)) :
    Arena.nativeIsRec kinds = ConLeche.nativeIsRec (kinds.map (·.map kindOf)) := by
  simp only [Arena.nativeIsRec, ConLeche.nativeIsRec, List.any_map]
  congr 1
  funext ks
  simp only [Function.comp_apply, List.any_map]
  congr 1
  funext k
  cases k <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:105-108 nativeCaps
The capability record the completed parts license.

`sorry`: `nativeCapsAt_spec` (`Bridge/Inductives/SumInstall.lean`) at
`nativeIsRec p.kinds`, through `nativeIsRec_spec` above. -/
theorem nativeCaps_spec (p : Arena.NativeParts) (q : ConLeche.NativeParts) :
    PSpec (fun st => PartsRel st p q)
      (Arena.nativeCaps p) (RCaps (ConLeche.nativeCaps q)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:110-128 nativeRawRec
The SYNTACTIC reading of `is_rec` off the declared constructor types, before
anything is normalised (task #268's first pass runs at this verdict).

`sorry`: `mentionsConst_spec` under the constructors' telescopes. -/
theorem nativeRawRec_spec (p : Arena.NativeParts) (q : ConLeche.NativeParts) :
    PSpec (fun st => PartsRel st p q)
      (Arena.nativeRawRec p) (RV (ConLeche.nativeRawRec q)) := by
  sorry

/-! ## `mentionsFvar`, memoised

`mentionsFvarIns` has NO statement of its own — it is the memo-insert helper
(con-leche's `Expr.mentionsFvarIns`), census class (S), and its content is
inside the walk's invariant step. -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:221-257 Expr.mentionsFvarGo
The memoised walk; note the `fvar` arm answers on the LEVEL and does not
descend into the variable's type, which is con-leche's own clause.

`sorry`: a fuel induction with the memo threaded, in
`Bridge/ExprOps/Walks.lean`'s shape. -/
theorem mentionsFvarGo_spec (q : Nat) (memo : Std.HashMap EIdx Bool)
    (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ FvarMemoOK q memo st)
      (Arena.mentionsFvarGo q memo fuel h)
      (fun st r => r.1 = Expr.mentionsFvar q hP ∧ FvarMemoOK q r.2 st) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:379-381 Expr.mentionsFvarFast
The entry at an empty memo.

`sorry`: `mentionsFvarGo_spec`. -/
theorem mentionsFvar_spec (q : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.mentionsFvar q e) (RV (Expr.mentionsFvar q eP)) := by
  sorry

/-! ## The opened re-check -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
One constructor's field kinds re-checked on the STORED (normalised) type, with
the binders opened at free variables.

`sorry`: `piBinders_spec`, `recFieldKind_spec`, `mentionsFvar_spec` and
`recFamOk_spec`, over the telescope. -/
theorem nativeOpenedOk_spec (fe₀ : IFEnv) (env₀ : Env) (T : NIdx)
    (TP : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP nIdx : Nat) (cty : EIdx) (ctyP : Expr) (nF : Nat)
    (ks : List Arena.RecFieldKind) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st cty = some ctyP ∧ denoteFEnv st fe₀ = some env₀)
      (Arena.nativeOpenedOk fe₀ T lps nP nIdx cty nF ks)
      (RV (ConLeche.nativeOpenedOk env₀ TP lpsP nP nIdx ctyP nF
        (ks.map kindOf))) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
The same over the whole constructor list.

`sorry`: a list zip induction over `nativeOpenedOk_spec`. -/
theorem nativeFieldsOk_spec (fe₀ : IFEnv) (env₀ : Env) (T : NIdx)
    (TP : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP nIdx : Nat) (ctorsA : List (IConstantVal × Nat))
    (ctorsAP : List (ConstantVal × Nat))
    (kinds : List (List Arena.RecFieldKind)) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors st ctorsA = some ctorsAP ∧ denoteFEnv st fe₀ = some env₀)
      (Arena.nativeFieldsOk fe₀ T lps nP nIdx ctorsA kinds)
      (RV (ConLeche.nativeFieldsOk env₀ TP lpsP nP nIdx ctorsAP
        (kinds.map (·.map kindOf)))) := by
  sorry

/-! ## The generated recursor and its rules -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
The `k` generated right-hand sides from `j` up, each annotated and compared.

`sorry`: `structRecRhsR_spec` (`Bridge/Inductives/NativeParts.lean`),
`unwrapOr`'s spec and `CoreSpec.knot`'s `annotate` slot, over a `Nat`
recursion. -/
theorem checkNativeRules_spec {μ : CheckMode} {env : Env} (feR : IFEnv)
    (envR : Env) (hk : CoreSpec μ Arena.checkFuel) (rlps : List NIdx)
    (rlpsP : List ConLeche.Name) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (elim : NIdx)
    (elimP : ConLeche.Name) (large : Bool) (nP nIdx : Nat) (tty : EIdx)
    (ttyP : Expr) (ctors : List (NIdx × Nat × EIdx × List Nat))
    (ctorsP : List (ConLeche.Name × Nat × Expr × List Nat)) (recC : NIdx)
    (recCP : ConLeche.Name) (rlvls : LsIdx) (rlvlsP : List Level) (k j : Nat) :
    CSpec μ env feR
      (fun st => Frontend.denoteNList st.ns rlps = some rlpsP ∧
        denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteCtors4 st ctors = some ctorsP ∧
        denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧
        denoteFEnv st feR = some envR ∧ denoteFEnv st feR = some env)
      (Arena.checkNativeRules feR rlps T lps elim large nP nIdx tty ctors recC
        rlvls k j)
      (fun st r => ∃ rhssP,
        ConLeche.checkNativeRules (m := CheckM) envR rlpsP TP lpsP elimP large
          nP nIdx ttyP ctorsP recCP rlvlsP k j = .ok rhssP ∧
        Frontend.denoteEList st r = some rhssP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
**The recursor generated, annotated and compared with the stream's.**

`sorry`: `structRecTyR_spec`, `checkNativeRules_spec`, `nativeCtors4_spec`
and `CoreSpec.knot`'s `annotate`/`defeq` slots. -/
theorem checkNativeRec_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (p : Arena.NativeParts)
    (q : ConLeche.NativeParts) (cvTa : IConstantVal) (cvTaP : ConstantVal)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat)) :
    CSpec μ env fe
      (fun st => PartsRel st p q ∧ Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st ctorsA = some ctorsAP ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeRec μ fe p cvTa ctorsA)
      (fun st r => ∃ F cvRaP rhssP,
        ConLeche.checkNativeRec (ConLeche.fueledOps μ F) env q cvTaP ctorsAP
          = .ok (cvRaP, rhssP) ∧
        Frontend.denoteCV st r.1 = some cvRaP ∧
        Frontend.denoteEList st r.2 = some rhssP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:504-519 checkNativeTable
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
The projection table at a structure-like block, at the tagged tower's offset
`1`.

`sorry`: `structProjGuards_spec` and `checkStructProjTable_spec`
(`Bridge/Inductives/StructInstall.lean`); the non-structure branch is the
identity on the index, so `InstRel` is `Pushed.refl`. -/
theorem checkNativeTable_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (p : Arena.NativeParts) (q : ConLeche.NativeParts)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat))
    (sortss : List (List LIdx)) (sortssP : List (List Level)) :
    CSpec μ env fe
      (fun st => PartsRel st p q ∧ denoteCtors st ctorsA = some ctorsAP ∧
        denoteLLists st sortss = some sortssP ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeTable p ctorsA sortss fe)
      (InstRel fe (fun env' =>
        @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env
          = .ok env')) := by
  sorry

/-! ## The pass -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:521-537 NativePass
What one pass yields, denoting con-leche's record at `E = Env`. -/
structure PassRel (q : ConLeche.NativePass Env) (st : EStore)
    (r : Arena.NativePass) : Prop where
  env₁ : denoteFEnv st r.env₁ = some q.env₁
  cvTa : Frontend.denoteCV st r.cvTa = some q.cvTa
  p : PartsRel st r.p q.p
  ctorsA : denoteCtors st r.ctorsA = some q.ctorsA
  sortss : denoteLLists st r.sortss = some q.sortss

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
`recCtorKindsAll` is the twin's spelling of con-leche's `ctorsA.mapM
(recCtorKinds …)` at the `Option` monad (the twin of `recCtorKinds` is monadic
in `AM` and optional in its result, so the `mapM` cannot be written).

`sorry`: a list induction over `recCtorKinds_spec`
(`Bridge/Inductives/NativeParts.lean`). -/
theorem recCtorKindsAll_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors st cs = some csP)
      (Arena.recCtorKindsAll T lps nP nIdx cs)
      (ROp RKss (csP.mapM (ConLeche.recCtorKinds TP lpsP nP nIdx))) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
The kinds classified on the stored constructors, with the two declines
(`negative`, `unsupported`) raised.

`sorry`: `recCtorKindsAll_spec`. -/
theorem classifyFixKinds_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat)) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors st ctorsA = some ctorsAP)
      (Arena.classifyFixKinds T lps nP nIdx ctorsA)
      (fun _ r => ∃ ks,
        ConLeche.classifyFixKinds (m := CheckM) TP lpsP nP nIdx ctorsAP
          = .ok ks ∧ r.map (·.map kindOf) = ks) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
**One pass over the former and the constructors** at a given `is_rec` verdict,
with the flag that says whether the classification confirms it.

`sorry`: `checkSumInd_spec`, `complete_spec`, `flushCaches_spec`
(`Bridge/Specs.lean`, closed, with `CacheOK.of_empty`), `checkSumCtors_spec`,
`classifyFixKinds_spec`, `withKinds_spec`, `nativeCaps_spec` and
`nativeCapsAt_spec`. -/
theorem checkNativePass_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (p₀ : Arena.NativeParts)
    (q₀ : ConLeche.NativeParts) (isRec : Bool) :
    CSpec μ env fe
      (fun st => PartsRel st p₀ q₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkNativePass μ fe p₀ isRec)
      (fun st r => ∃ F qP settled,
        ConLeche.checkNativePass (ConLeche.fueledOps μ F) env q₀ isRec
          = .ok (qP, settled) ∧
        PassRel qP st r.1 ∧ r.2 = settled ∧
        InstRel fe (fun e => e = qP.env₁) st r.1.env₁) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
**The install after the pass**: the elimination restriction, the index
binders' sorts, the kinds re-checked, the stream's rules against the generated
ones, the constructors consed, the recursor with its rules, and the projection
table.

`sorry`: `readLevel`'s spec (`Bridge/Specs.lean`, closed),
`openPisAtFvars`' spec, `checkStructFieldSortsI_spec`, `nativeFieldsOk_spec`,
`paramLevels_spec`, `nativeRulesOk_spec`, `consSumCtors_spec`,
`checkNativeRec_spec`, `sumRules_spec` and `checkNativeTable_spec` — the
longest single composition of the tier. -/
theorem checkNativeTail_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (r : Arena.NativePass)
    (qP : ConLeche.NativePass Env) :
    CSpec μ env fe
      (fun st => PassRel qP st r ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeTail μ fe r)
      (InstRel fe (fun env' => ∃ F,
        ConLeche.checkNativeTail (ConLeche.fueledOps μ F) env qP = .ok env')) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
**THE FIXPOINT ROUTE**, one of the two `checkIndDecl` dispatches to.  The
distinct names, the pass at the syntactic `is_rec`, and — where that reading
overshot — a second pass at the classification's verdict.

`sorry`: `nativeRawRec_spec`, `checkNativePass_spec` twice,
`nativeIsRec_spec` (closed), `checkNativeTail_spec`, and the `Nodup` guard,
which is `denoteN_inj` at the constructor names (`Bridge/Rel.lean`). -/
theorem checkNative_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (p₀ : Arena.NativeParts)
    (q₀ : ConLeche.NativeParts) :
    CSpec μ env fe
      (fun st => PartsRel st p₀ q₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkNative μ fe p₀)
      (InstRel fe (fun env' => ∃ F,
        ConLeche.checkNative (ConLeche.fueledOps μ F) env q₀ = .ok env')) := by
  sorry

end ConRon.Bridge.Inductives
