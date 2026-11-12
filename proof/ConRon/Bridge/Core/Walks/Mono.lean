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
module

public import ConLeche.Verify.Mono
public import ConLeche.Verify.Fueled
/- `fst_tac`/`snd_tac` close the projection equations by `rfl` through
`pairFns`'s body, which con-leche's `Verify/PairM` (a plain `public section`)
does not expose; `import all` makes it visible to these proofs. -/
import all ConLeche.Verify.PairM

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false

open ConLeche

variable {mode : CheckMode} {eager : Bool} {env : Env} {r₁ r₂ : CoreFns CheckM}

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
ι telescope certificate** (`iotaCase3At`'s case 3), a `List` recursion over `r.infer` and
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

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the η-expansion
of a partially applied constructor. -/
theorem structEtaExpand_mono (h : FnsRefines r₁ r₂) (k d : Nat) (a b t : Expr) :
    MRefines (structEtaExpand r₁ env k d a b t) (structEtaExpand r₂ env k d a b t) := by
  have := (structEtaExpand (pairFns r₁ r₂ h) env k d a b t).property
  rwa [structEtaExpand_fst_proj, structEtaExpand_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — structure η. -/
theorem structEtaCert_mono (h : FnsRefines r₁ r₂) (d : Nat) (a b : Expr) :
    MRefines (structEtaCert r₁ env d a b) (structEtaCert r₂ env d a b) := by
  have := (structEtaCert (pairFns r₁ r₂ h) env d a b).property
  rwa [structEtaCert_fst_proj, structEtaCert_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — is a
proposition. -/
theorem isPropType_mono (h : FnsRefines r₁ r₂) (d : Nat) (T : Expr) :
    MRefines (isPropType r₁ d T) (isPropType r₂ d T) := by
  have := (isPropType (pairFns r₁ r₂ h) d T).property
  rwa [isPropType_fst_proj, isPropType_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — is a type
unit-like. -/
theorem unitLikeLoop_mono (h : FnsRefines r₁ r₂) (n d : Nat) (T : Expr) :
    MRefines (unitLikeLoop r₁ env n d T) (unitLikeLoop r₂ env n d T) := by
  have := (unitLikeLoop (pairFns r₁ r₂ h) env n d T).property
  rwa [unitLikeLoop_fst_proj, unitLikeLoop_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the field loop
at the unit-like loop's budget `m`. -/
theorem unitLikeFields_mono (h : FnsRefines r₁ r₂) (m n d : Nat) (t : Expr) :
    MRefines (unitLikeFields r₁ (unitLikeLoop r₁ env m) n d t)
      (unitLikeFields r₂ (unitLikeLoop r₂ env m) n d t) := by
  have := (unitLikeFields (pairFns r₁ r₂ h) (unitLikeLoop (pairFns r₁ r₂ h) env m) n d t).property
  rwa [unitLikeFields_fst_proj (fun d e => unitLikeLoop_fst_proj m d e),
    unitLikeFields_snd_proj (fun d e => unitLikeLoop_snd_proj m d e)] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the structure
arm at the unit-like loop's budget `m`. -/
theorem unitLikeStruct_mono (h : FnsRefines r₁ r₂) (m d : Nat) (w : Expr) :
    MRefines (unitLikeStruct r₁ (unitLikeLoop r₁ env m) env d w)
      (unitLikeStruct r₂ (unitLikeLoop r₂ env m) env d w) := by
  have := (unitLikeStruct (pairFns r₁ r₂ h) (unitLikeLoop (pairFns r₁ r₂ h) env m) env d w).property
  rwa [unitLikeStruct_fst_proj (fun d e => unitLikeLoop_fst_proj m d e),
    unitLikeStruct_snd_proj (fun d e => unitLikeLoop_snd_proj m d e)] at this

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
theorem majorToCtor_mono (h : FnsRefines r₁ r₂) (d : Nat) (c : Name) (isK : Bool)
    (rules : List RecRule) (e : Expr) :
    MRefines (majorToCtor mode r₁ env d c isK rules e) (majorToCtor mode r₂ env d c isK rules e) := by
  have := (majorToCtor mode (pairFns r₁ r₂ h) env d c isK rules e).property
  rwa [majorToCtor_fst_proj, majorToCtor_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the literal
major's constructor form. -/
theorem litMajorToCtor_mono (h : FnsRefines r₁ r₂) (d : Nat) (e : Expr) :
    MRefines (litMajorToCtor r₁ env d e) (litMajorToCtor r₂ env d e) := by
  have := (litMajorToCtor (pairFns r₁ r₂ h) env d e).property
  rwa [litMajorToCtor_fst_proj, litMajorToCtor_snd_proj] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — the major
prepared for the rule. -/
theorem prepareMajor_mono (h : FnsRefines r₁ r₂) (d : Nat) (c : Name) (isK : Bool)
    (rules : List RecRule) (e : Expr) :
    MRefines (prepareMajor mode r₁ env d c isK rules e) (prepareMajor mode r₂ env d c isK rules e) := by
  have := (prepareMajor mode (pairFns r₁ r₂ h) env d c isK rules e).property
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
innermost level of the binder-telescope comparison. -/
theorem defeqBindersInner_mono (h : FnsRefines r₁ r₂) (lam : Bool) (d : Nat) (b₁ b₂ : Expr) :
    MRefines (defeqBindersInner mode r₁ lam d b₁ b₂) (defeqBindersInner mode r₂ lam d b₁ b₂) := by
  have := (defeqBindersInner mode (pairFns r₁ r₂ h) lam d b₁ b₂).property
  rwa [defeqBindersInner_fst, defeqBindersInner_snd] at this

/-- con-leche: ConLeche/Verify/Mono.lean:52 whnfCoreBody_mono — **the
binder-telescope comparison** at an arbitrary descent budget. -/
theorem defeqBinders_mono (h : FnsRefines r₁ r₂) (lam : Bool) (n d : Nat) (fvs : List Expr)
    (ty₁ body₁ ty₂ body₂ : Expr) :
    MRefines (defeqBinders mode r₁ lam n d fvs ty₁ body₁ ty₂ body₂)
      (defeqBinders mode r₂ lam n d fvs ty₁ body₁ ty₂ body₂) := by
  have := (defeqBinders mode (pairFns r₁ r₂ h) lam n d fvs ty₁ body₁ ty₂ body₂).property
  rwa [defeqBinders_fst, defeqBinders_snd] at this

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
`pureFns mode eager env fuel`, which is exactly what `Bridge/Core/Walks/Spec.lean`'s
five answer relations take, so these are stated at the same spelling the
`Sim*Op` conclusions use. -/

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`reduceNat`. -/
theorem reduceNatFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e : Expr} {r : Option Expr}
    (hr : reduceNatFueled mode eager env f d e = .ok r) :
    reduceNatFueled mode eager env f' d e = .ok r :=
  reduceNat_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`iotaCertsFull`. -/
theorem iotaCertsFullFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {ty : Expr} {args : List Expr} {r : Bool}
    (hr : iotaCertsFullFueled mode eager env f d ty args = .ok r) :
    iotaCertsFullFueled mode eager env f' d ty args = .ok r :=
  iotaCertsFull_mono (pureFns_mono env hle) d ty args r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defEqList`. -/
theorem defEqListFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {as bs : List Expr} {r : Bool}
    (hr : defEqListFueled mode eager env f d as bs = .ok r) :
    defEqListFueled mode eager env f' d as bs = .ok r :=
  defEqList_mono (pureFns_mono env hle) d as bs r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`iotaIndexOk`. -/
theorem iotaIndexOkFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {mI rP cnP : Nat} {tyCtor : Expr} {margs idx : List Expr} {r : Bool}
    (hr : iotaIndexOkFueled mode eager env f d mI rP cnP tyCtor margs idx = .ok r) :
    iotaIndexOkFueled mode eager env f' d mI rP cnP tyCtor margs idx = .ok r :=
  iotaIndexOk_mono (pureFns_mono env hle) d mI rP cnP tyCtor margs idx r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`proofIrrel`. -/
theorem proofIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : proofIrrelFueled mode eager env f d a b = .ok r) :
    proofIrrelFueled mode eager env f' d a b = .ok r :=
  proofIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`propIrrel`. -/
theorem propIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : propIrrelFueled mode eager env f d a b = .ok r) :
    propIrrelFueled mode eager env f' d a b = .ok r :=
  propIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`structEtaCertWith`. -/
theorem structEtaCertWithFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b wtb : Expr} {r : Bool}
    (hr : structEtaCertWithFueled mode eager env f d a b wtb = .ok r) :
    structEtaCertWithFueled mode eager env f' d a b wtb = .ok r :=
  structEtaCertWith_mono (pureFns_mono env hle) d a b wtb r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`structEtaExpand`. -/
theorem structEtaExpandFueled_mono {f f' : Nat} (hle : f ≤ f') {k d : Nat} {a b t : Expr}
    {r : Bool} (hr : structEtaExpandFueled mode eager env f k d a b t = .ok r) :
    structEtaExpandFueled mode eager env f' k d a b t = .ok r :=
  structEtaExpand_mono (pureFns_mono env hle) k d a b t r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`isPropType`. -/
theorem isPropTypeFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {T : Expr} {r : Bool}
    (hr : isPropTypeFueled mode eager env f d T = .ok r) :
    isPropTypeFueled mode eager env f' d T = .ok r :=
  isPropType_mono (pureFns_mono env hle) d T r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`unitLikeLoop`. -/
theorem unitLikeLoopFueled_mono {f f' : Nat} (hle : f ≤ f') {n d : Nat} {T : Expr} {r : Bool}
    (hr : unitLikeLoopFueled mode eager env f n d T = .ok r) :
    unitLikeLoopFueled mode eager env f' n d T = .ok r :=
  unitLikeLoop_mono (pureFns_mono env hle) n d T r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`unitLikeFields`, the loop at budget `m` for its `ul`. -/
theorem unitLikeFieldsFueled_mono {f f' : Nat} (hle : f ≤ f') {m n d : Nat} {t : Expr}
    {r : Bool}
    (hr : unitLikeFields (pureFns mode eager env f) (unitLikeLoopFueled mode eager env f m) n d t
      = .ok r) :
    unitLikeFields (pureFns mode eager env f') (unitLikeLoopFueled mode eager env f' m) n d t
      = .ok r :=
  unitLikeFields_mono (pureFns_mono env hle) m n d t r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`unitLikeStruct`, the loop at budget `m` for its `ul`. -/
theorem unitLikeStructFueled_mono {f f' : Nat} (hle : f ≤ f') {m d : Nat} {w : Expr}
    {r : Bool}
    (hr : unitLikeStruct (pureFns mode eager env f) (unitLikeLoopFueled mode eager env f m) env d w
      = .ok r) :
    unitLikeStruct (pureFns mode eager env f') (unitLikeLoopFueled mode eager env f' m) env d w
      = .ok r :=
  unitLikeStruct_mono (pureFns_mono env hle) m d w r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`structEtaCert`. -/
theorem structEtaCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : structEtaCertFueled mode eager env f d a b = .ok r) :
    structEtaCertFueled mode eager env f' d a b = .ok r :=
  structEtaCert_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`structUnitCert`. -/
theorem structUnitCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : structUnitCertFueled mode eager env f d a b = .ok r) :
    structUnitCertFueled mode eager env f' d a b = .ok r :=
  structUnitCert_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`etaCert`. -/
theorem etaCertFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {ty body b : Expr} {r : Bool}
    (hr : etaCertFueled mode eager env f d ty body b = .ok r) :
    etaCertFueled mode eager env f' d ty body b = .ok r :=
  etaCert_mono (pureFns_mono env hle) d ty body b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`stuckIrrel`. -/
theorem stuckIrrelFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : stuckIrrelFueled mode eager env f d a b = .ok r) :
    stuckIrrelFueled mode eager env f' d a b = .ok r :=
  stuckIrrel_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`majorToCtor`. -/
theorem majorToCtorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {c : Name} {isK : Bool}
    {rules : List RecRule} {e r : Expr}
    (hr : majorToCtorFueled mode eager env f d c isK rules e = .ok r) :
    majorToCtorFueled mode eager env f' d c isK rules e = .ok r :=
  majorToCtor_mono (pureFns_mono env hle) d c isK rules e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`litMajorToCtor`. -/
theorem litMajorToCtorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e r : Expr}
    (hr : litMajorToCtorFueled mode eager env f d e = .ok r) :
    litMajorToCtorFueled mode eager env f' d e = .ok r :=
  litMajorToCtor_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`prepareMajor`. -/
theorem prepareMajorFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {c : Name} {isK : Bool}
    {rules : List RecRule} {e r : Expr}
    (hr : prepareMajorFueled mode eager env f d c isK rules e = .ok r) :
    prepareMajorFueled mode eager env f' d c isK rules e = .ok r :=
  prepareMajor_mono (pureFns_mono env hle) d c isK rules e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`boolTrueShortcut`. -/
theorem boolTrueShortcutFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {e : Expr} {r : Bool}
    (hr : boolTrueShortcutFueled mode eager env f d e = .ok r) :
    boolTrueShortcutFueled mode eager env f' d e = .ok r :=
  boolTrueShortcut_mono (pureFns_mono env hle) d e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defeqSpine`. -/
theorem defeqSpineFueled_mono {f f' : Nat} (hle : f ≤ f') {d : Nat} {a b : Expr} {r : Bool}
    (hr : defeqSpineFueled mode eager env f d a b = .ok r) :
    defeqSpineFueled mode eager env f' d a b = .ok r :=
  defeqSpine_mono (pureFns_mono env hle) d a b r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defeqBindersInner`. -/
theorem defeqBindersInnerFueled_mono {f f' : Nat} (hle : f ≤ f') {lam : Bool} {d : Nat}
    {b₁ b₂ : Expr} {r : Bool}
    (hr : defeqBindersInnerFueled mode eager env f lam d b₁ b₂ = .ok r) :
    defeqBindersInnerFueled mode eager env f' lam d b₁ b₂ = .ok r :=
  defeqBindersInner_mono (pureFns_mono env hle) lam d b₁ b₂ r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the merge at
`defeqBinders`. -/
theorem defeqBindersFueled_mono {f f' : Nat} (hle : f ≤ f') {lam : Bool} {n d : Nat}
    {fvs : List Expr} {ty₁ body₁ ty₂ body₂ : Expr} {r : Bool}
    (hr : defeqBindersFueled mode eager env f lam n d fvs ty₁ body₁ ty₂ body₂ = .ok r) :
    defeqBindersFueled mode eager env f' lam n d fvs ty₁ body₁ ty₂ body₂ = .ok r :=
  defeqBinders_mono (pureFns_mono env hle) lam n d fvs ty₁ body₁ ty₂ body₂ r hr

/-- con-leche: ConLeche/Verify/Mono.lean:125 whnf_mono — **the merge
`whnfBody_spec` needs**, at an arbitrary step budget: the `whnf` loop's own
recursion hands out one existential per iteration and this is what makes them
one. -/
theorem whnfLoopFueled_mono {f f' : Nat} (hle : f ≤ f') {d n : Nat}
    {e r : Expr} (hr : whnfLoop (pureFns mode eager env f) env d n e = .ok r) :
    whnfLoop (pureFns mode eager env f') env d n e = .ok r :=
  whnfLoop_mono (pureFns_mono env hle) d n e r hr

/-- con-leche: ConLeche/Verify/Mono.lean:135 isDefEqCore_mono — the same merge
at the lazy-delta PROJECTION loop. -/
theorem lazyDeltaProjReductionFueled_mono {f f' : Nat} (hle : f ≤ f')
    {d : Nat} {sn : Name} {i n : Nat} {a b : Expr} {r : Bool}
    (hr : lazyDeltaProjReduction mode (pureFns mode eager env f) env d sn i n a b
      = .ok r) :
    lazyDeltaProjReduction mode (pureFns mode eager env f') env d sn i n a b = .ok r :=
  lazyDeltaProjReduction_mono (pureFns_mono env hle) d sn i n a b r hr

/-! ## 3b. The walks to a family's sort and the projection guard

These take the knot's slots as plain functions (`wh`, `inf`) rather than the
record, so con-leche has no `PairM` projection for them; its `FueledM`
family carries the monotonicity in its `.property`, and `Verify/Fueled.lean`'s
`…_atF` reads it back at the pure record. -/

/-- con-leche: ConLeche/Verify/Fueled.lean:223 formerSortLoop_atF — the merge at
the walk to a family's sort. -/
theorem formerSortLoopFueled_mono {f f' : Nat} (hle : f ≤ f') {d n : Nat} {e : Expr}
    {r : Option Level}
    (hr : formerSortLoop (pureFns mode eager env f).whnf d n e = .ok r) :
    formerSortLoop (pureFns mode eager env f').whnf d n e = .ok r := by
  have h := (formerSortLoop (fueledFns mode eager env).whnf d n e).property (v := r) hle
  rw [formerSortLoop_atF, formerSortLoop_atF] at h
  exact h hr

/-- con-leche: ConLeche/Verify/Fueled.lean:239 formerNeverZeroAt_atF — the merge
at the never-zero test. -/
theorem formerNeverZeroAtFueled_mono {f f' : Nat} (hle : f ≤ f') {cvT : ConstantVal}
    {caps : IndCaps} {us : List Level} {r : Bool}
    (hr : formerNeverZeroAt (pureFns mode eager env f).whnf cvT caps us = .ok r) :
    formerNeverZeroAt (pureFns mode eager env f').whnf cvT caps us = .ok r := by
  have h := (formerNeverZeroAt (fueledFns mode eager env).whnf cvT caps us).property
    (v := r) hle
  rw [formerNeverZeroAt_atF, formerNeverZeroAt_atF] at h
  exact h hr

/-- con-leche: ConLeche/Verify/Fueled.lean:249 iotaCase3At_atF — the merge at
the ι case split. -/
theorem iotaCase3AtFueled_mono {f f' : Nat} (hle : f ≤ f') {isK : Bool}
    {induct : Name} {us : List Level} {r : Bool}
    (hr : iotaCase3At (pureFns mode eager env f).whnf env.find? isK induct us = .ok r) :
    iotaCase3At (pureFns mode eager env f').whnf env.find? isK induct us = .ok r := by
  have h := (iotaCase3At (fueledFns mode eager env).whnf env.find? isK induct us).property
    (v := r) hle
  rw [iotaCase3At_atF, iotaCase3At_atF] at h
  exact h hr

/-- con-leche: ConLeche/Verify/Fueled.lean:262 projGuardSort_atF — the merge at
the projection guard's sort. -/
theorem projGuardSortFueled_mono {f f' : Nat} (hle : f ≤ f') {cvT : ConstantVal}
    {caps : IndCaps} {us : List Level} {r : Option Level}
    (hr : projGuardSort (pureFns mode eager env f).whnf cvT caps us = .ok r) :
    projGuardSort (pureFns mode eager env f').whnf cvT caps us = .ok r := by
  have h := (projGuardSort (fueledFns mode eager env).whnf cvT caps us).property
    (v := r) hle
  rw [projGuardSort_atF, projGuardSort_atF] at h
  exact h hr

/-- con-leche: ConLeche/Verify/Fueled.lean:206 checkGuardRows_atF — the merge at
the guard's rows. -/
theorem checkGuardRowsFueled_mono {f f' : Nat} (hle : f ≤ f') {g : Level}
    {rows : List (Nat × Expr)} {r : Unit}
    (hr : checkGuardRows (pureFns mode eager env f).inferIO (pureFns mode eager env f).whnf
      g rows = .ok r) :
    checkGuardRows (pureFns mode eager env f').inferIO (pureFns mode eager env f').whnf
      g rows = .ok r := by
  have h := (checkGuardRows (fueledFns mode eager env).inferIO
    (fueledFns mode eager env).whnf g rows).property (v := r) hle
  rw [checkGuardRows_atF, checkGuardRows_atF] at h
  exact h hr

/-- con-leche: ConLeche/Verify/Fueled.lean:272 checkProjGuard_atF — the merge at
the projection guard. -/
theorem checkProjGuardFueled_mono {f f' : Nat} (hle : f ≤ f') {entry : ProjEntry}
    {us : List Level} {r : Unit}
    (hr : checkProjGuard (pureFns mode eager env f).inferIO (pureFns mode eager env f).whnf
      env entry us = .ok r) :
    checkProjGuard (pureFns mode eager env f').inferIO (pureFns mode eager env f').whnf
      env entry us = .ok r := by
  have h := (checkProjGuard (fueledFns mode eager env).inferIO
    (fueledFns mode eager env).whnf env entry us).property (v := r) hle
  rw [checkProjGuard_atF, checkProjGuard_atF] at h
  exact h hr

/-! ## 4. The axiom census -/

section Census

#print axioms defEqList_mono
#print axioms defEqListFueled_mono
#print axioms whnfLoopFueled_mono
#print axioms lazyDeltaProjReductionFueled_mono
#print axioms formerSortLoopFueled_mono
#print axioms iotaCase3AtFueled_mono
#print axioms checkProjGuardFueled_mono

end Census

end ConRon.Bridge.Core
