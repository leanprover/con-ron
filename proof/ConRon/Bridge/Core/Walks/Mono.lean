/-
# `ConRon.Bridge.Core.Walks.Mono` — the fuel merge

DESIGN §8's `### Task #97-P3-CoreWalks` §6.1 names this module's contents and
prices them.  The fuel existential sits inside the answer relation, so
con-leche's `FueledM` wrapper is not needed for a body: a walk that calls the
knot ONCE per clause hands its `∃ F` straight out.  **A LOOP is different.**
A walk that calls the knot in a `List` recursion (`defEqList`,
`iotaCertsFull`) or in a fuel loop (`whnfLoop`, `lazyDeltaReduction`,
`lazyDeltaProjReduction`) gets one existential per iteration and has to merge
them into one — which is exactly `Verify/Mono.lean`'s job.  con-leche has
`isDefEqCore_mono` and `pureFns_mono`; it does NOT have `defEqList_mono`,
because its own proof never needs one (`FueledM` does the merging).  So the
bridge needs one `…_mono` per LOOPING walk, each ten lines in
`Verify/Mono.lean`'s own shape.

This module supplies them, for **every** knot-calling helper of
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
`whnfLoopFueled_mono` / `lazyDeltaProjReductionFueled_mono` — the two that
`whnfBody_spec` and `defeqBody_spec` rest on (DESIGN §6.1).

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
projections.  Ordered as `ConLeche/Kernel/Core.lean` orders the definitions.
(`projCert`/`projCertAt` read only the environment — the syntactic
`teleArityOk` — so they need none.) -/

/-- con-leche: ConLeche/Verify/PairM.lean:351 fst_tac — `boolTrueShortcut`'s
first projection (con-leche proves the pair inline in `defeqBody_fst_proj`;
the bridge's merge wants it named). -/
theorem boolTrueShortcut_fst_proj (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    (boolTrueShortcut (pairFns r₁ r₂ h) d e).val.1 = boolTrueShortcut r₁ d e := by
  unfold boolTrueShortcut
  fst_tac

/-- con-leche: ConLeche/Verify/PairM.lean:369 snd_tac — and its second. -/
theorem boolTrueShortcut_snd_proj (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    (boolTrueShortcut (pairFns r₁ r₂ h) d e).val.2 = boolTrueShortcut r₂ d e := by
  unfold boolTrueShortcut
  snd_tac

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the literal
acceleration refines at a refined record. -/
theorem reduceNat_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (reduceNat r₁ env d e) (reduceNat r₂ env d e) := by
  have := (reduceNat (pairFns r₁ r₂ h) env d e).property
  rwa [reduceNat_fst_proj, reduceNat_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the full-grade
ι telescope certificate** (`iotaCase3`), a `List` recursion over `r.infer` and
`r.defeq`. -/
theorem iotaCertsFull_mono (h : FnsRefines r₁ r₂) (d : Nat) (ty : Expr) (args : List Expr) :
    MRefines (iotaCertsFull r₁ env d ty args) (iotaCertsFull r₂ env d ty args) := by
  have := (iotaCertsFull (pairFns r₁ r₂ h) env d ty args).property
  rwa [iotaCertsFull_fst, iotaCertsFull_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
pairwise spine comparison**, the walk DESIGN §6.1 names first and the one
`defEqList_spec` needs. -/
theorem defEqList_mono (h : FnsRefines r₁ r₂) (d : Nat) (as bs : List Expr) :
    MRefines (defEqList r₁ env d as bs) (defEqList r₂ env d as bs) := by
  have := (defEqList (pairFns r₁ r₂ h) env d as bs).property
  rwa [defEqList_fst, defEqList_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the ι index
comparison, `defEqList` under a residual. -/
theorem iotaIndexOk_mono (h : FnsRefines r₁ r₂) (d mI rP cnP : Nat) (tyCtor : Expr) (margs idx : List Expr) :
    MRefines (iotaIndexOk r₁ env d mI rP cnP tyCtor margs idx) (iotaIndexOk r₂ env d mI rP cnP tyCtor margs idx) := by
  have := (iotaIndexOk (pairFns r₁ r₂ h) env d mI rP cnP tyCtor margs idx).property
  rwa [iotaIndexOk_fst, iotaIndexOk_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — proof
irrelevance at a known proposition. -/
theorem proofIrrel_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (proofIrrel r₁ d a b) (proofIrrel r₂ d a b) := by
  have := (proofIrrel (pairFns r₁ r₂ h) d a b).property
  rwa [proofIrrel_fst_proj, proofIrrel_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the hoisted
proof-irrelevance test. -/
theorem propIrrel_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (propIrrel r₁ env d a b) (propIrrel r₂ env d a b) := by
  have := (propIrrel (pairFns r₁ r₂ h) env d a b).property
  rwa [propIrrel_fst_proj, propIrrel_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the η
certificate against a GIVEN reduced type. -/
theorem structEtaCertWith_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b wtb : Expr) :
    MRefines (structEtaCertWith r₁ env d a b wtb) (structEtaCertWith r₂ env d a b wtb) := by
  have := (structEtaCertWith (pairFns r₁ r₂ h) env d a b wtb).property
  rwa [structEtaCertWith_fst_proj, structEtaCertWith_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — structure η. -/
theorem structEtaCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (structEtaCert r₁ env d a b) (structEtaCert r₂ env d a b) := by
  have := (structEtaCert (pairFns r₁ r₂ h) env d a b).property
  rwa [structEtaCert_fst_proj, structEtaCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the unit
certificate. -/
theorem structUnitCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (structUnitCert r₁ env d a b) (structUnitCert r₂ env d a b) := by
  have := (structUnitCert (pairFns r₁ r₂ h) env d a b).property
  rwa [structUnitCert_fst_proj, structUnitCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — η at a λ
against a non-λ, with the verified mode's T2 tax. -/
theorem etaCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (ty body : Expr) (b : Expr) :
    MRefines (etaCert mode r₁ env d ty body b) (etaCert mode r₂ env d ty body b) := by
  have := (etaCert mode (pairFns r₁ r₂ h) env d ty body b).property
  rwa [etaCert_fst_proj, etaCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the fallback
at two stuck terms. -/
theorem stuckIrrel_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (stuckIrrel r₁ env d a b) (stuckIrrel r₂ env d a b) := by
  have := (stuckIrrel (pairFns r₁ r₂ h) env d a b).property
  rwa [stuckIrrel_fst_proj, stuckIrrel_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the
stuck-major fabrication. -/
theorem majorToCtor_mono (h : FnsRefines r₁ r₂) (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    MRefines (majorToCtor mode r₁ env d c rules e) (majorToCtor mode r₂ env d c rules e) := by
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
theorem prepareMajor_mono (h : FnsRefines r₁ r₂) (d : Nat) (c : Name) (rules : List RecRule) (e : Expr) :
    MRefines (prepareMajor mode r₁ env d c rules e) (prepareMajor mode r₂ env d c rules e) := by
  have := (prepareMajor mode (pairFns r₁ r₂ h) env d c rules e).property
  rwa [prepareMajor_fst_proj, prepareMajor_snd_proj] at this

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

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the
innermost level of the λ-telescope comparison. -/
theorem defeqLamsInner_mono (h : FnsRefines r₁ r₂) (d : Nat) (b₁ b₂ : Expr) :
    MRefines (defeqLamsInner mode r₁ d b₁ b₂) (defeqLamsInner mode r₂ d b₁ b₂) := by
  have := (defeqLamsInner mode (pairFns r₁ r₂ h) d b₁ b₂).property
  rwa [defeqLamsInner_fst, defeqLamsInner_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
λ-telescope comparison** at an arbitrary descent budget. -/
theorem defeqLams_mono (h : FnsRefines r₁ r₂) (n d : Nat) (ty₁ body₁ ty₂ body₂ : Expr) :
    MRefines (defeqLams mode r₁ n d ty₁ body₁ ty₂ body₂) (defeqLams mode r₂ n d ty₁ body₁ ty₂ body₂) := by
  have := (defeqLams mode (pairFns r₁ r₂ h) n d ty₁ body₁ ty₂ body₂).property
  rwa [defeqLams_fst, defeqLams_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
reduction loop at an ARBITRARY step budget**, which is what `whnfBody_spec`'s
`Nat` induction needs and which con-leche's `whnfBody_mono` gives only at
`whnfLoopFuel`. -/
theorem whnfLoop_mono (h : FnsRefines r₁ r₂) (d n : Nat) (e : Expr) :
    MRefines (whnfLoop r₁ env d n e) (whnfLoop r₂ env d n e) := by
  have := (whnfLoop (pairFns r₁ r₂ h) env d n e).property
  rwa [whnfLoop_fst_proj, whnfLoop_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
lazy-delta PROJECTION loop at an arbitrary step budget**. -/
theorem lazyDeltaProjReduction_mono (h : FnsRefines r₁ r₂) (d : Nat)
    (sn : Name) (i n : Nat) (a b : Expr) :
    MRefines (lazyDeltaProjReduction mode r₁ env d sn i n a b)
      (lazyDeltaProjReduction mode r₂ env d sn i n a b) := by
  have := (lazyDeltaProjReduction mode (pairFns r₁ r₂ h) env d sn i n a b).property
  rwa [lazyDeltaProjReduction_fst_proj, lazyDeltaProjReduction_snd_proj] at this

/-! ## 2. The fueled corollaries — THE MERGE

`Verify/Mono.lean`'s own "Fueled corollaries" section, at the walks.  Every
one is `pureFns_mono` fed to §1, and every one has the shape a bridge proof
calls at: *an answer produced at fuel `f` is produced at any `f' ≥ f`*.

`ConLeche.…Fueled` (`Verify/Knot.lean:165-256`) is the walk applied to
`pureFns mode env fuel`, which is exactly what `Bridge/Core/Walks/Spec.lean`'s
five answer relations take, so these are stated at the same spelling the
`Sim*Op` conclusions use. -/

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`reduceNat`. -/
theorem reduceNatFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e : Expr} {r : Option Expr}
    (hr : reduceNatFueled mode env f d e = .ok r) :
    reduceNatFueled mode env f' d e = .ok r :=
  reduceNat_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`iotaCertsFull`. -/
theorem iotaCertsFullFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {ty : Expr} {args : List Expr} {r : Bool}
    (hr : iotaCertsFullFueled mode env f d ty args = .ok r) :
    iotaCertsFullFueled mode env f' d ty args = .ok r :=
  iotaCertsFull_mono (pureFns_mono env hle) d ty args r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defEqList`. -/
theorem defEqListFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {as bs : List Expr} {r : Bool}
    (hr : defEqListFueled mode env f d as bs = .ok r) :
    defEqListFueled mode env f' d as bs = .ok r :=
  defEqList_mono (pureFns_mono env hle) d as bs r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`iotaIndexOk`. -/
theorem iotaIndexOkFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {mI rP cnP : Nat} {tyCtor : Expr} {margs idx : List Expr} {r : Bool}
    (hr : iotaIndexOkFueled mode env f d mI rP cnP tyCtor margs idx = .ok r) :
    iotaIndexOkFueled mode env f' d mI rP cnP tyCtor margs idx = .ok r :=
  iotaIndexOk_mono (pureFns_mono env hle) d mI rP cnP tyCtor margs idx r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`proofIrrel`. -/
theorem proofIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : proofIrrelFueled mode env f d a b = .ok r) :
    proofIrrelFueled mode env f' d a b = .ok r :=
  proofIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`propIrrel`. -/
theorem propIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : propIrrelFueled mode env f d a b = .ok r) :
    propIrrelFueled mode env f' d a b = .ok r :=
  propIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`structEtaCertWith`. -/
theorem structEtaCertWithFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b wtb : Expr} {r : Bool}
    (hr : structEtaCertWithFueled mode env f d a b wtb = .ok r) :
    structEtaCertWithFueled mode env f' d a b wtb = .ok r :=
  structEtaCertWith_mono (pureFns_mono env hle) d a b wtb r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`structEtaCert`. -/
theorem structEtaCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : structEtaCertFueled mode env f d a b = .ok r) :
    structEtaCertFueled mode env f' d a b = .ok r :=
  structEtaCert_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`structUnitCert`. -/
theorem structUnitCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : structUnitCertFueled mode env f d a b = .ok r) :
    structUnitCertFueled mode env f' d a b = .ok r :=
  structUnitCert_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`etaCert`. -/
theorem etaCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {ty body b : Expr} {r : Bool}
    (hr : etaCertFueled mode env f d ty body b = .ok r) :
    etaCertFueled mode env f' d ty body b = .ok r :=
  etaCert_mono (pureFns_mono env hle) d ty body b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`stuckIrrel`. -/
theorem stuckIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : stuckIrrelFueled mode env f d a b = .ok r) :
    stuckIrrelFueled mode env f' d a b = .ok r :=
  stuckIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`majorToCtor`. -/
theorem majorToCtorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {c : Name} {rules : List RecRule} {e r : Expr}
    (hr : majorToCtorFueled mode env f d c rules e = .ok r) :
    majorToCtorFueled mode env f' d c rules e = .ok r :=
  majorToCtor_mono (pureFns_mono env hle) d c rules e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`litMajorToCtor`. -/
theorem litMajorToCtorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e r : Expr}
    (hr : litMajorToCtorFueled mode env f d e = .ok r) :
    litMajorToCtorFueled mode env f' d e = .ok r :=
  litMajorToCtor_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`prepareMajor`. -/
theorem prepareMajorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {c : Name} {rules : List RecRule} {e r : Expr}
    (hr : prepareMajorFueled mode env f d c rules e = .ok r) :
    prepareMajorFueled mode env f' d c rules e = .ok r :=
  prepareMajor_mono (pureFns_mono env hle) d c rules e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`boolTrueShortcut`. -/
theorem boolTrueShortcutFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e : Expr} {r : Bool}
    (hr : boolTrueShortcutFueled mode env f d e = .ok r) :
    boolTrueShortcutFueled mode env f' d e = .ok r :=
  boolTrueShortcut_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defeqSpine`. -/
theorem defeqSpineFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : defeqSpineFueled mode env f d a b = .ok r) :
    defeqSpineFueled mode env f' d a b = .ok r :=
  defeqSpine_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defeqLamsInner`. -/
theorem defeqLamsInnerFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {b₁ b₂ : Expr} {r : Bool}
    (hr : defeqLamsInnerFueled mode env f d b₁ b₂ = .ok r) :
    defeqLamsInnerFueled mode env f' d b₁ b₂ = .ok r :=
  defeqLamsInner_mono (pureFns_mono env hle) d b₁ b₂ r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defeqLams`. -/
theorem defeqLamsFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {n : Nat} {ty₁ body₁ ty₂ body₂ : Expr} {r : Bool}
    (hr : defeqLamsFueled mode env f n d ty₁ body₁ ty₂ body₂ = .ok r) :
    defeqLamsFueled mode env f' n d ty₁ body₁ ty₂ body₂ = .ok r :=
  defeqLams_mono (pureFns_mono env hle) n d ty₁ body₁ ty₂ body₂ r hr

/-- con-leche: ConLeche/Verify/Mono.lean:125 whnf_mono — **the merge
`whnfBody_spec` needs**, at an arbitrary step budget: the `whnf` loop's own
recursion hands out one existential per iteration and this is what makes them
one. -/
theorem whnfLoopFueled_mono {f f' : Nat} (hle : f ≤ f') {d n : Nat}
    {e r : Expr} (hr : whnfLoop (pureFns mode env f) env d n e = .ok r) :
    whnfLoop (pureFns mode env f') env d n e = .ok r :=
  whnfLoop_mono (pureFns_mono env hle) d n e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the same merge
at the lazy-delta PROJECTION loop. -/
theorem lazyDeltaProjReductionFueled_mono {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {sn : Name} {i n : Nat} {a b : Expr} {r : Bool}
    (hr : lazyDeltaProjReduction mode (pureFns mode env f) env d sn i n a b
      = .ok r) :
    lazyDeltaProjReduction mode (pureFns mode env f') env d sn i n a b = .ok r :=
  lazyDeltaProjReduction_mono (pureFns_mono env hle) d sn i n a b r hr

/-! ## 4. The axiom census -/

section Census

#print axioms defEqList_mono
#print axioms defEqListFueled_mono
#print axioms whnfLoopFueled_mono
#print axioms lazyDeltaProjReductionFueled_mono

end Census

end ConRon.Bridge.Core
