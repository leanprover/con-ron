/-
# `ConRon.Bridge.Checker.Hyp` — the two named hypotheses

The capstone of this tier carries exactly two hypotheses that are not
discharged here, and they are the two tiers this one does not own.  The
precedent is the original campaign's `conron.model_exists`
(`proof/ConRon/RefineOld/Main.lean:174`), which carried `hk` and `hind` in the
same position for the same reason.

**`CoreSpec μ F` — the CORE tier's.**  Its main field is **`Bridge/Core/
Knot.lean`'s own `KnotSpec`**, taken as written (task #97-P3-Core landed while
this round ran): the six slots of `ConRon.Arena.coreKnot mode fe id f` against
con-leche's six fueled entry points, at `CheckOK`/`Ext` with the `SimE`/`SimV`
answer relations and the `Expr.WScoped d e` precondition.  Nothing of it is
restated here — `Bridge/Core/Induction.lean`'s `knot_spec_checkFuel` is what
discharges it, and `CoreSpec.of_knot` below does that in one line.

**Two things `CoreSpec` adds, and why.**

1. **It quantifies over `env` and `fe`.**  `Bridge/Core`'s `knot_spec` fixes
   one environment; the FOLD's environment changes at every declaration.  Its
   `EnvWF env` hypothesis is P3-Core's `henv`, which is why `FoldOK`
   (`Bridge/Checker/Inv.lean`) carries `EnvWF` as a clause — con-leche's own
   join point (`Verify/Cached/BridgeC.lean:609`) carries it too.
2. **`ensureSortCore` is not a slot of `coreKnot`.**  `Arena/Core.lean` builds
   it on top (`ensureSort (pureFnsA mode fe fuel) fe depth e`) and the
   declaration front door calls it at every constant, so `EnsureSortSpec` is a
   second field, in `Bridge/Core/Knot.lean`'s `BodySpec` shape.  It is one
   `whnf` call and a tag test, so it is cheap and it is the Core tier's to
   discharge — **it should move into `Bridge/Core` when someone takes it.**

**What the Core tier's frame does not say, and this tier needs.**
`KnotSpec`'s postcondition is `CheckOK mode env fe s' ∧ Ext s₀.store s'.store`.
`CheckOK` carries `PinsOK s'`, so the pin table still DENOTES — but the fold
also needs `PersPins s'` (the pin handles are persistent), and that is
transported by `s'.pins = s₀.pins` and nothing else.  No core entry writes
`s.pins`, so the clause is free; `CoreStep` below carries it, and adding it to
`KnotSpec`'s postcondition was the one thing this tier asked of the Core tier.
**It is there** (task #97-P3-CoreWalks): every slot of `KnotSpec` and
`EnsureSortSpec` now ends `s'.pins = s₀.pins`, which is what lets the run-form
proofs of `Bridge/Checker/Base.lean` and `Bridge/Checker/Arms.lean` conclude
`CoreStep` at all.  Task #97-P3-Checker-2's stop-gap `CorePinFrame` — a
third field of `CoreSpec` saying the same thing — is deleted with this
merge.

**`IndSpec μ` — the INDUCTIVES tier's**.  `Arena/Inductives.lean`'s
`checkIndDecl` is 9 500 lines of arena twin under it, and `checkDecl`'s
`.indDecl` arm is the single place the declaration checker calls it.  So the
whole inductive install is one hypothesis, exactly as
`RefineOld/Main.lean`'s `hind : IndRoutesSpec .Verified` was.
-/
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Core.Induction
import ConRon.Bridge.Core.EnsureSort

open ConLeche ConRon.Arena Std.Do

namespace ConRon.Bridge

set_option autoImplicit false
set_option mvcgen.warning false

/-! ## What a core call leaves behind

Every clause of the Core tier's `KnotSpec` has the same frame: the invariant
survives at the SAME environment (a core call never installs) and the arena
only grows.  `CoreStep` is that frame plus the pin-table equation the module
note explains. -/

/-- con-leche: ConLeche/Verify/Cached/SimC.lean:366 SimC — what a core entry
point leaves behind: the invariant at the same environment, an append, and an
untouched pin table. -/
structure CoreStep (μ : CheckMode) (env : Env) (fe : IFEnv) (s s' : AState) :
    Prop where
  ok : CheckOK μ env fe s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins

theorem CoreStep.refl {μ : CheckMode} {env : Env} {fe : IFEnv} {s : AState}
    (h : CheckOK μ env fe s) : CoreStep μ env fe s s :=
  ⟨h, Ext.refl _, rfl⟩

theorem CoreStep.trans {μ : CheckMode} {env : Env} {fe : IFEnv} {a b c : AState}
    (h₁ : CoreStep μ env fe a b) (h₂ : CoreStep μ env fe b c) :
    CoreStep μ env fe a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, by rw [h₂.pins, h₁.pins]⟩

/-! ## The seventh entry point -/

/-- con-leche: none — the LEVEL-valued answer relation, for `ensureSort`.
`Bridge/Core/Knot.lean`'s `SimE` at a `Level` answer; no well-scopedness
conjunct, because a level has no binder depth. -/
def SimL (op : Nat → Nat → Expr → CheckM Level) (d : Nat) (e : Expr)
    (st' : EStore) (r : LIdx) : Prop :=
  ∃ u, denoteL st'.ls r = some u ∧ ∃ F, op F d e = .ok u

theorem SimL.ext {op : Nat → Nat → Expr → CheckM Level} {d : Nat} {e : Expr}
    {st st' : EStore} {r : LIdx} (h : SimL op d e st r) (hx : Ext st st') :
    SimL op d e st' r := by
  obtain ⟨u, hu, F, hF⟩ := h
  exact ⟨u, hx.lss.ls.lvl _ _ hu, F, hF⟩

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore — **the
seventh entry point, which is not a slot**.  `Bridge/Core/Knot.lean`'s
six-field `KnotSpec` does not cover it because `coreKnot` does not have it;
the declaration front door calls it at every constant, so this tier needs it.

Stated in `BodySpec`'s shape — a `Std.Do` triple — so that the Core tier can
discharge it with `mvcgen` like everything else it owns. -/
def EnsureSortSpec (mode : CheckMode) (env : Env) (fe : IFEnv) (f : Nat) :
    Prop :=
  ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => ⌜s = s₀⌝⦄ Arena.ensureSortCore mode fe f d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimL (ConLeche.ensureSortCore mode env) d e s'.store r⌝⦄

/-! ## The Core tier's theorem, as this tier uses it -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC — **THE CORE
TIER'S THEOREM, as this tier's hypothesis**: `Bridge/Core/Knot.lean`'s
`KnotSpec` at EVERY well-formed environment and its index, plus the seventh
entry point.

The quantification is the fold's: its environment changes at every
declaration while `Bridge/Core/Induction.lean`'s `knot_spec` fixes one. -/
structure CoreSpec (mode : CheckMode) (f : Nat) : Prop where
  knot : ∀ (env : Env) (fe : IFEnv), EnvWF env → Core.KnotSpec mode env fe f
  sort : ∀ (env : Env) (fe : IFEnv), EnvWF env → EnsureSortSpec mode env fe f

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC — **the Core
tier's half, discharged**: `Bridge/Core/Induction.lean`'s
`knot_spec_checkFuel` IS the `knot` field, so what the capstone still owes the
Core tier is `EnsureSortSpec` and nothing else.

This is the whole adapter the merge needed: the Core round's statement and
this round's hypothesis are the same statement, and one line joins them. -/
theorem CoreSpec.of_knot {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (hs : ∀ (env : Env) (fe : IFEnv), EnvWF env →
      EnsureSortSpec μ env fe Arena.checkFuel) :
    CoreSpec μ Arena.checkFuel :=
  ⟨fun _ _ henv => Core.knot_spec_checkFuel henv hμ, hs⟩

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore — **the
seventh entry point, discharged** (task #97-P3-CoreWalks, the Checker tier's
ask 2): `Bridge/Core/EnsureSort.lean`'s `ensureSortCore_spec` IS this
statement.  `SimL` there and `SimL` here are the same definition, which is
why this is one term. -/
theorem ensureSortSpec_of_knot {mode : CheckMode} {env : Env} {fe : IFEnv}
    {f : Nat} (hsim : Core.KnotSpec mode env fe f) :
    EnsureSortSpec mode env fe f :=
  fun s₀ d i e hok hden hw => Core.ensureSortCore_spec hsim s₀ d i e hok hden hw

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC — **`CoreSpec`
with NOTHING left to supply**: both fields come from `Bridge/Core`, so the
capstone's Core-tier hypothesis is discharged outright (modulo the six body
walks `KnotSpec` itself is still waiting on).  Task #97-P3-CoreWalks. -/
theorem CoreSpec.of_core {μ : CheckMode} (hμ : μ.verifiedChecks = true) :
    CoreSpec μ Arena.checkFuel :=
  CoreSpec.of_knot hμ
    (fun _ _ henv => ensureSortSpec_of_knot (Core.knot_spec_checkFuel henv hμ))

/-! ## The inductive install -/

/-- con-leche: ConLeche/Kernel/Checker.lean:440-609 checkDecl (the `.indDecl`
arm) — **THE INDUCTIVES TIER'S THEOREM, as this tier's hypothesis**.

The hypothesis `hpin` is the arena's own dispatch, already taken: this clause
covers the route `basisPinHit` did NOT recognise, which is the one
`Inductives.checkIndDecl` runs.  The recogniser's own exactness is
`Bridge/Checker/Basis.lean`'s and is not part of this hypothesis.

The precedent is `RefineOld/Main.lean`'s `hind : IndRoutesSpec .Verified`:
one named hypothesis for the whole inductive install, discharged by a tier of
its own.

**Two clauses corrected (task #97-P3-Ind's finding, made here in P3-Checker-2).**
The round that wrote this statement asked for `PersIFEnv fe'` and did not ask
for `Pushed fe fe'`, and the inductive tier found both wrong by trying to prove
them:

* `PersIFEnv fe'` is **false of this arm**.  `Arena/Checker.lean`'s bracket is
  `flushCaches; enterScratch; <the step>; promoteNew; dropScratch`, so
  `checkDecl` — and with it `Inductives.checkIndDecl` — runs with the scratch
  tier OPEN and every constant the route installs carries a freshly interned,
  hence scratch, type.  Persistence is `promoteNew`'s, one level up.
  `Bridge/Checker/Decl.lean`'s `DeclOut` says exactly this in prose and omits
  the clause; this statement contradicted it.
* `Pushed fe fe'` was **missing**, and the consumer needs it:
  `checkDecl_bridge_ind`'s conclusion is `DeclOut`, whose `pushed` clause is
  what makes `checkDeclStep`'s promotion counter `k` mean "the constants this
  step installed", and only the arm can supply it.

The edit is consumer-compatible — `Bridge/Checker/Capstone.lean` never reads
`IndSpec`, it passes it to `checkDecl_bridge_ind` — and with it
`Bridge/Inductives/Decl.lean`'s `indSpec_of_bridge` closes with no `sorry` of
its own. 
**`EnvWF env'`, added** (task #97-P3-Ind round 7, the coordinator's
authorised conclusion change): the fold boundary after a declaration needs
the pushed index's environment well formed (task #97-P3-Checker round 9's
finding); `Bridge/Inductives/Rel.lean`'s `IndOut` carries the same clause and
`indSpec_of_bridge` passes it through. -/
structure IndSpec (μ : CheckMode) : Prop where
  run : ∀ {env : Env} {fe fe' : IFEnv} {s s' : AState}
      {block : List IConstantInfo} {b : List ConstantInfo} {nP : Nat}
      {pinsP : List NatOpPinSet},
    FoldOK μ env fe s → Frontend.denoteCIList s.store block = some b →
    ConLeche.basisPinHit b = none →
    Inductives.checkIndDecl μ fe block nP s = .ok (fe', s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧ fe.visibleBelow ≤ fe'.visibleBelow ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
        ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.indDecl b nP)
          = .ok env' ∧ EnvWF env'

/-! ## One reader inversion both siblings want

`Bridge/Checker/Base.lean` and `Bridge/Checker/Canon.lean` are siblings of
this module and both walk the expression store, so `view`'s run form lives
here rather than in either of them. -/

/-- con-leche: none — `view`'s inversion, off `Bridge/Specs.lean`'s triple.
(`Bridge/Inductives/Rel.lean` has the same three lines under the name
`view_run`, one tier ABOVE this one, so this tier carries its own; it lives
here rather than in `Base.lean` or `Canon.lean` because BOTH siblings walk
the expression store.) -/
theorem viewE_run {h : EIdx} {s s' : AState} {v : ENodeView}
    (hr : view h s = .ok (v, s')) : s' = s ∧ s.store.view h = some v :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ s.store.view h = some r) rfl hr (view_spec s h)

end ConRon.Bridge
