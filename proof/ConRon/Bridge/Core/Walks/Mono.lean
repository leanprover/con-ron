/-
# `ConRon.Bridge.Core.Walks.Mono` — the fuel merge

Task #97-P3-Core-2.  DESIGN §8's `### Task #97-P3-CoreWalks` §6.1 names this
module's contents and prices them:

> Task #97-P3-Core's §2 recorded that *"con-leche's `FueledM` wrapper is not
> needed … the fuel existential sits inside the answer relation and `mvcgen`
> never touches it."*  **That is true of a body and false of a LOOP.**  A walk
> that calls the knot ONCE per clause hands its `∃ F` straight out.  A walk
> that calls it in a `List` recursion (`defEqList`, `iotaCerts`,
> `structEtaProjCerts`) or in a fuel loop (`whnfLoop`, `defeqLoop`) gets one
> existential per iteration and has to merge them into one — which is exactly
> `Verify/Mono.lean`'s job.  con-leche has `isDefEqCore_mono` and
> `pureFns_mono`; it does NOT have `defEqList_mono`, because its own proof
> never needed one (`FueledM` did the merging).  So the bridge owes one
> `…_mono` per LOOPING walk, each ten lines in `Verify/Mono.lean`'s own shape.

This module pays that debt, and pays it for **every** knot-calling helper of
`ConLeche/Kernel/Core.lean` rather than only the looping ones — because the
cost of the non-looping rows is one line each and a body theorem that merges
two arms' existentials wants them all in hand.

## The shape, which is con-leche's

`Verify/Mono.lean` derives `whnfCoreBody_mono` … `ensureSort_mono` from the
relational pair monad: `PairM refinesRel` carries the refinement in its
`.property`, `pairFns r₁ r₂ h` is the paired record, and
`Verify/PairM.lean`'s `<walk>_fst_proj` / `_snd_proj` say that running the
walk at the paired record projects to running it at each component.  So

```lean
theorem defEqList_mono (h : FnsRefines r₁ r₂) (d : Nat) (as bs : List Expr) :
    MRefines (defEqList r₁ env d as bs) (defEqList r₂ env d as bs) := by
  have := (defEqList (pairFns r₁ r₂ h) env d as bs).property
  rwa [defEqList_fst, defEqList_snd] at this
```

is the whole proof, and `Verify/PairM.lean` already has the two projections
for **every** walk below — con-leche built them for its own six bodies and
they cover the helpers on the way down.  What con-leche never wrote is the
`MRefines` corollary and the FUELED corollary, which is the half the bridge
actually calls.

## What a caller does with it

At a `List` recursion the bridge holds the head's `∃ F₁` (from
`KnotSpec.defeq`, say) and the tail's `∃ F₂` (from the induction
hypothesis).  It takes `F := max F₁ F₂`, lifts the head with con-leche's own
`isDefEqCore_mono` and the tail with `defEqListFueled_mono` below, and then
the step equation applies at ONE fuel.  The same at a fuel loop, with
`whnfLoopFueled_mono` / `defeqLoopFueled_mono` — and those two are the debt
DESIGN §6.1 says sits unpaid under `whnfBody_spec` and `defeqBody_spec`.

**This module mentions no arena state at all**: it is pure con-leche, and it
imports `ConLeche.Verify.Mono` and nothing of `ConRon.Arena`.  That is why it
is the cheapest module of the tier and why nothing in it can break when the
twin moves.
-/
import ConRon.Bridge.Core.Walks.Spec
import ConLeche.Verify.Mono

namespace ConRon.Bridge.Core

set_option autoImplicit false

open ConLeche

variable {mode : CheckMode} {env : Env} {r₁ r₂ : CoreFns CheckM}

/-! ## 1. The record-level monotonicity, one per knot-calling walk

Each is `Verify/Mono.lean`'s `whnfCoreBody_mono` with the walk's own pair of
projections.  Ordered as `ConLeche/Kernel/Core.lean` orders the definitions. -/

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the literal
acceleration refines at a refined record. -/
theorem reduceNat_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (reduceNat r₁ env d e) (reduceNat r₂ env d e) := by
  have := (reduceNat (pairFns r₁ r₂ h) env d e).property
  rwa [reduceNat_fst_proj, reduceNat_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the ι
spine certificate**, a `List` recursion over `r.inferIO` and `r.defeq`: one
of the three walks DESIGN §6.1 names. -/
theorem iotaCerts_mono (h : FnsRefines r₁ r₂) (d : Nat) (lic : Bool)
    (ty : Expr) (args : List Expr) :
    MRefines (iotaCerts r₁ env d lic ty args)
      (iotaCerts r₂ env d lic ty args) := by
  have := (iotaCerts (pairFns r₁ r₂ h) env d lic ty args).property
  rwa [iotaCerts_fst, iotaCerts_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
pairwise spine comparison**, the walk DESIGN §6.1 names first and the one
`defEqList_spec` needs. -/
theorem defEqList_mono (h : FnsRefines r₁ r₂) (d : Nat) (as bs : List Expr) :
    MRefines (defEqList r₁ env d as bs) (defEqList r₂ env d as bs) := by
  have := (defEqList (pairFns r₁ r₂ h) env d as bs).property
  rwa [defEqList_fst, defEqList_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the ι index
comparison, `defEqList` under a residual. -/
theorem iotaIndexOk_mono (h : FnsRefines r₁ r₂) (d mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) :
    MRefines (iotaIndexOk r₁ env d mI rP cnP tyCtor margs idx)
      (iotaIndexOk r₂ env d mI rP cnP tyCtor margs idx) := by
  have := (iotaIndexOk (pairFns r₁ r₂ h) env d mI rP cnP tyCtor margs
    idx).property
  rwa [iotaIndexOk_fst, iotaIndexOk_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — proof
irrelevance at a known proposition. -/
theorem proofIrrel_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (proofIrrel r₁ env d a b) (proofIrrel r₂ env d a b) := by
  have := (proofIrrel (pairFns r₁ r₂ h) env d a b).property
  rwa [proofIrrel_fst_proj, proofIrrel_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the hoisted
proof-irrelevance test. -/
theorem propIrrel_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (propIrrel r₁ env d a b) (propIrrel r₂ env d a b) := by
  have := (propIrrel (pairFns r₁ r₂ h) env d a b).property
  rwa [propIrrel_fst_proj, propIrrel_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
structure-η field certificates**, a `List Nat` recursion: the third of DESIGN
§6.1's looping walks. -/
theorem structEtaProjCerts_mono (h : FnsRefines r₁ r₂) (d : Nat) (T : Name)
    (us' : List Level) (targs : List Expr) (b : Expr) (lpsT : List Name)
    (idxs : List Nat) :
    MRefines (structEtaProjCerts r₁ env d T us' targs b lpsT idxs)
      (structEtaProjCerts r₂ env d T us' targs b lpsT idxs) := by
  have := (structEtaProjCerts (pairFns r₁ r₂ h) env d T us' targs b lpsT
    idxs).property
  rwa [structEtaProjCerts_fst, structEtaProjCerts_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the η
certificate against a GIVEN reduced type. -/
theorem structEtaCertWith_mono (h : FnsRefines r₁ r₂) (d : Nat)
    (a b wtb : Expr) :
    MRefines (structEtaCertWith mode r₁ env d a b wtb)
      (structEtaCertWith mode r₂ env d a b wtb) := by
  have := (structEtaCertWith mode (pairFns r₁ r₂ h) env d a b wtb).property
  rwa [structEtaCertWith_fst_proj, structEtaCertWith_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — structure η. -/
theorem structEtaCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (structEtaCert mode r₁ env d a b)
      (structEtaCert mode r₂ env d a b) := by
  have := (structEtaCert mode (pairFns r₁ r₂ h) env d a b).property
  rwa [structEtaCert_fst_proj, structEtaCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the unit
certificate. -/
theorem structUnitCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (structUnitCert r₁ env d a b) (structUnitCert r₂ env d a b) := by
  have := (structUnitCert (pairFns r₁ r₂ h) env d a b).property
  rwa [structUnitCert_fst_proj, structUnitCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — η at a λ
against a non-λ. -/
theorem etaCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (ty body : Expr)
    (mb : BinderMeta) (b : Expr) :
    MRefines (etaCert mode r₁ env d ty body mb b)
      (etaCert mode r₂ env d ty body mb b) := by
  have := (etaCert mode (pairFns r₁ r₂ h) env d ty body mb b).property
  rwa [etaCert_fst_proj, etaCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the fallback
at two stuck terms. -/
theorem stuckIrrel_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (stuckIrrel mode r₁ env d a b)
      (stuckIrrel mode r₂ env d a b) := by
  have := (stuckIrrel mode (pairFns r₁ r₂ h) env d a b).property
  rwa [stuckIrrel_fst_proj, stuckIrrel_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the
stuck-major fabrication. -/
theorem majorToCtor_mono (h : FnsRefines r₁ r₂) (d : Nat) (c : Name)
    (rules : List RecRule) (e : Expr) :
    MRefines (majorToCtor mode r₁ env d c rules e)
      (majorToCtor mode r₂ env d c rules e) := by
  have := (majorToCtor mode (pairFns r₁ r₂ h) env d c rules e).property
  rwa [majorToCtor_fst_proj, majorToCtor_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the literal
major's constructor form. -/
theorem litMajorToCtor_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (litMajorToCtor r₁ env d e) (litMajorToCtor r₂ env d e) := by
  have := (litMajorToCtor (pairFns r₁ r₂ h) env d e).property
  rwa [litMajorToCtor_fst_proj, litMajorToCtor_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the major
prepared for the rule. -/
theorem prepareMajor_mono (h : FnsRefines r₁ r₂) (d : Nat) (c : Name)
    (rules : List RecRule) (e : Expr) :
    MRefines (prepareMajor mode r₁ env d c rules e)
      (prepareMajor mode r₂ env d c rules e) := by
  have := (prepareMajor mode (pairFns r₁ r₂ h) env d c rules e).property
  rwa [prepareMajor_fst_proj, prepareMajor_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the
string-literal scrutinee's expansion. -/
theorem projLitToCtor_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (projLitToCtor r₁ env d e) (projLitToCtor r₂ env d e) := by
  have := (projLitToCtor (pairFns r₁ r₂ h) env d e).property
  rwa [projLitToCtor_fst_proj, projLitToCtor_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the
projection's fire certificate. -/
theorem projCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (lic : Bool)
    (c : Name) (us : List Level) (args : List Expr) :
    MRefines (projCert r₁ env d lic c us args)
      (projCert r₂ env d lic c us args) := by
  have := (projCert (pairFns r₁ r₂ h) env d lic c us args).property
  rwa [projCert_fst_proj, projCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the same as
the mode runs it. -/
theorem projCertAt_mono (h : FnsRefines r₁ r₂) (d : Nat) (v lic : Bool)
    (c : Name) (us : List Level) (args : List Expr) :
    MRefines (projCertAt r₁ env d v lic c us args)
      (projCertAt r₂ env d v lic c us args) := by
  have := (projCertAt (pairFns r₁ r₂ h) env d v lic c us args).property
  rwa [projCertAt_fst_proj, projCertAt_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — one ι step. -/
theorem iotaRec_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (iotaRec mode r₁ env d e) (iotaRec mode r₂ env d e) := by
  have := (iotaRec mode (pairFns r₁ r₂ h) env d e).property
  rwa [iotaRec_fst_proj, iotaRec_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the
`Bool.true` short-circuit. -/
theorem boolTrueShortcut_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (boolTrueShortcut r₁ d e) (boolTrueShortcut r₂ d e) := by
  have := (boolTrueShortcut (pairFns r₁ r₂ h) d e).property
  rwa [boolTrueShortcut_fst_proj, boolTrueShortcut_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — two
applications of the same constant. -/
theorem defeqSpine_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (defeqSpine r₁ env d a b) (defeqSpine r₂ env d a b) := by
  have := (defeqSpine (pairFns r₁ r₂ h) env d a b).property
  rwa [defeqSpine_fst, defeqSpine_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
reduction loop at an ARBITRARY step budget**, which is what `whnfBody_spec`'s
`Nat` induction needs and which con-leche's `whnfBody_mono` gives only at
`whnfLoopFuel`. -/
theorem whnfLoop_mono (h : FnsRefines r₁ r₂) (d n : Nat) (e : Expr) :
    MRefines (whnfLoop r₁ env d n e) (whnfLoop r₂ env d n e) := by
  have := (whnfLoop (pairFns r₁ r₂ h) env d n e).property
  rwa [whnfLoop_fst_proj, whnfLoop_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
lazy-delta loop at an arbitrary step budget**, the same debt at
`defeqBody_spec`. -/
theorem defeqLoop_mono (h : FnsRefines r₁ r₂) (d n : Nat) (pi : Bool)
    (a b : Expr) :
    MRefines (defeqLoop mode r₁ env d n pi a b)
      (defeqLoop mode r₂ env d n pi a b) := by
  have := (defeqLoop mode (pairFns r₁ r₂ h) env d n pi a b).property
  rwa [defeqLoop_fst_proj, defeqLoop_snd_proj] at this

/-! ## 2. The fueled corollaries — THE MERGE

`Verify/Mono.lean`'s own "Fueled corollaries" section, at the walks.  Every
one is `pureFns_mono` fed to §1, and every one has the shape a bridge proof
calls at: *an answer produced at fuel `f` is produced at any `f' ≥ f`*.

`ConLeche.…Fueled` (`Verify/Knot.lean:218-332`) is the walk applied to
`pureFns mode env fuel`, which is exactly what `Bridge/Core/Walks/Spec.lean`'s
five answer relations take, so these are stated at the same spelling the
`Sim*Op` conclusions use. -/

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
`reduceNat`. -/
theorem reduceNatFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e : Expr}
    {r : Option Expr} (hr : reduceNatFueled mode env f d e = .ok r) :
    reduceNatFueled mode env f' d e = .ok r :=
  reduceNat_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the ι spine certificate. -/
theorem iotaCertsFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {lic : Bool} {ty : Expr} {args : List Expr} {r : Bool}
    (hr : iotaCertsFueled mode env f d lic ty args = .ok r) :
    iotaCertsFueled mode env f' d lic ty args = .ok r :=
  iotaCerts_mono (pureFns_mono env hle) d lic ty args r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — **the merge
`defEqList_spec` needs**: DESIGN §8's `### Task #97-P3-CoreWalks` §6.1 in one
line. -/
theorem defEqListFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {as bs : List Expr} {r : Bool}
    (hr : defEqListFueled mode env f d as bs = .ok r) :
    defEqListFueled mode env f' d as bs = .ok r :=
  defEqList_mono (pureFns_mono env hle) d as bs r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the ι index comparison. -/
theorem iotaIndexOkFueled_mono {f f' : Nat} (hle : f ≤ f')
    {d mI rP cnP : Nat} {tyCtor : Expr} {margs idx : List Expr} {r : Bool}
    (hr : iotaIndexOkFueled mode env f d mI rP cnP tyCtor margs idx = .ok r) :
    iotaIndexOkFueled mode env f' d mI rP cnP tyCtor margs idx = .ok r :=
  iotaIndexOk_mono (pureFns_mono env hle) d mI rP cnP tyCtor margs idx r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
proof irrelevance. -/
theorem proofIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {a b : Expr} {r : Bool}
    (hr : proofIrrelFueled mode env f d a b = .ok r) :
    proofIrrelFueled mode env f' d a b = .ok r :=
  proofIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the hoisted proof-irrelevance test. -/
theorem propIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {a b : Expr} {r : Bool}
    (hr : propIrrelFueled mode env f d a b = .ok r) :
    propIrrelFueled mode env f' d a b = .ok r :=
  propIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the η field certificates. -/
theorem structEtaProjCertsFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
    {lpsT : List Name} {idxs : List Nat} {r : Bool}
    (hr : structEtaProjCertsFueled mode env f d T us' targs b lpsT idxs
      = .ok r) :
    structEtaProjCertsFueled mode env f' d T us' targs b lpsT idxs = .ok r :=
  structEtaProjCerts_mono (pureFns_mono env hle) d T us' targs b lpsT idxs r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the η certificate with a given reduced type. -/
theorem structEtaCertWithFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {a b wtb : Expr} {r : Bool}
    (hr : structEtaCertWithFueled mode env f d a b wtb = .ok r) :
    structEtaCertWithFueled mode env f' d a b wtb = .ok r :=
  structEtaCertWith_mono (pureFns_mono env hle) d a b wtb r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
structure η. -/
theorem structEtaCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {a b : Expr} {r : Bool}
    (hr : structEtaCertFueled mode env f d a b = .ok r) :
    structEtaCertFueled mode env f' d a b = .ok r :=
  structEtaCert_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the unit certificate. -/
theorem structUnitCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {a b : Expr} {r : Bool}
    (hr : structUnitCertFueled mode env f d a b = .ok r) :
    structUnitCertFueled mode env f' d a b = .ok r :=
  structUnitCert_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
η. -/
theorem etaCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {ty body : Expr} {mb : BinderMeta} {b : Expr} {r : Bool}
    (hr : etaCertFueled mode env f d ty body mb b = .ok r) :
    etaCertFueled mode env f' d ty body mb b = .ok r :=
  etaCert_mono (pureFns_mono env hle) d ty body mb b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the stuck fallback. -/
theorem stuckIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {a b : Expr} {r : Bool}
    (hr : stuckIrrelFueled mode env f d a b = .ok r) :
    stuckIrrelFueled mode env f' d a b = .ok r :=
  stuckIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the stuck-major fabrication. -/
theorem majorToCtorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {c : Name} {rules : List RecRule} {e r : Expr}
    (hr : majorToCtorFueled mode env f d c rules e = .ok r) :
    majorToCtorFueled mode env f' d c rules e = .ok r :=
  majorToCtor_mono (pureFns_mono env hle) d c rules e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the literal major. -/
theorem litMajorToCtorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {e r : Expr} (hr : litMajorToCtorFueled mode env f d e = .ok r) :
    litMajorToCtorFueled mode env f' d e = .ok r :=
  litMajorToCtor_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the prepared major. -/
theorem prepareMajorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {c : Name} {rules : List RecRule} {e r : Expr}
    (hr : prepareMajorFueled mode env f d c rules e = .ok r) :
    prepareMajorFueled mode env f' d c rules e = .ok r :=
  prepareMajor_mono (pureFns_mono env hle) d c rules e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the literal scrutinee's expansion. -/
theorem projLitToCtorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {e r : Expr} (hr : projLitToCtorFueled mode env f d e = .ok r) :
    projLitToCtorFueled mode env f' d e = .ok r :=
  projLitToCtor_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the projection certificate. -/
theorem projCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {lic : Bool} {c : Name} {us : List Level} {args : List Expr} {r : Bool}
    (hr : projCertFueled mode env f d lic c us args = .ok r) :
    projCertFueled mode env f' d lic c us args = .ok r :=
  projCert_mono (pureFns_mono env hle) d lic c us args r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the mode's projection certificate. -/
theorem projCertAtFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {v lic : Bool} {c : Name} {us : List Level} {args : List Expr} {r : Bool}
    (hr : projCertAtFueled mode env f d v lic c us args = .ok r) :
    projCertAtFueled mode env f' d v lic c us args = .ok r :=
  projCertAt_mono (pureFns_mono env hle) d v lic c us args r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the ι step. -/
theorem iotaRecFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e : Expr}
    {r : Option Expr} (hr : iotaRecFueled mode env f d e = .ok r) :
    iotaRecFueled mode env f' d e = .ok r :=
  iotaRec_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the `Bool.true` short-circuit. -/
theorem boolTrueShortcutFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {e : Expr} {r : Bool}
    (hr : boolTrueShortcutFueled mode env f d e = .ok r) :
    boolTrueShortcutFueled mode env f' d e = .ok r :=
  boolTrueShortcut_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the constant-headed spine. -/
theorem defeqSpineFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat}
    {a b : Expr} {r : Bool}
    (hr : defeqSpineFueled mode env f d a b = .ok r) :
    defeqSpineFueled mode env f' d a b = .ok r :=
  defeqSpine_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:148 whnf_mono — **the merge
`whnfBody_spec` needs**, at an arbitrary step budget: the `whnf` loop's own
recursion hands out one existential per iteration and this is what makes them
one. -/
theorem whnfLoopFueled_mono {f f' : Nat} (hle : f ≤ f') {d n : Nat}
    {e r : Expr} (hr : whnfLoop (pureFns mode env f) env d n e = .ok r) :
    whnfLoop (pureFns mode env f') env d n e = .ok r :=
  whnfLoop_mono (pureFns_mono env hle) d n e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — **the merge
`defeqBody_spec` needs**, at an arbitrary lazy-delta budget. -/
theorem defeqLoopFueled_mono {f f' : Nat} (hle : f ≤ f') {d n : Nat}
    {pi : Bool} {a b : Expr} {r : Bool}
    (hr : defeqLoop mode (pureFns mode env f) env d n pi a b = .ok r) :
    defeqLoop mode (pureFns mode env f') env d n pi a b = .ok r :=
  defeqLoop_mono (pureFns_mono env hle) d n pi a b r hr

/-! ## 3. The two-existential merge, once

Every caller of §2 does the same three lines — take `max`, lift each side,
apply the step equation — so the pattern is worth a name.  `Nat.le_max_left`
and `Nat.le_max_right` are the only arithmetic in the tier. -/

/-- con-leche: none — **the merge idiom**: two answers produced at their own
fuels are produced at one.  The two monotonicity facts are supplied by the
caller from §2 (or from `Verify/Mono.lean`), which is what keeps this lemma
free of any walk's name. -/
theorem merge2 {α β : Type} {P : Nat → CheckM α} {Q : Nat → CheckM β}
    {x : α} {y : β}
    (hP : ∀ {f f' : Nat}, f ≤ f' → ∀ {v : α}, P f = .ok v → P f' = .ok v)
    (hQ : ∀ {f f' : Nat}, f ≤ f' → ∀ {v : β}, Q f = .ok v → Q f' = .ok v)
    (hx : ∃ F, P F = .ok x) (hy : ∃ F, Q F = .ok y) :
    ∃ F, P F = .ok x ∧ Q F = .ok y := by
  obtain ⟨F₁, h₁⟩ := hx
  obtain ⟨F₂, h₂⟩ := hy
  exact ⟨max F₁ F₂, hP (Nat.le_max_left F₁ F₂) h₁,
    hQ (Nat.le_max_right F₁ F₂) h₂⟩

/-! ## 4. The axiom census -/

section Census

#print axioms defEqList_mono
#print axioms defEqListFueled_mono
#print axioms whnfLoopFueled_mono
#print axioms defeqLoopFueled_mono
#print axioms merge2

end Census

end ConRon.Bridge.Core
