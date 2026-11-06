/-
# `ConRon.Bridge.Checker.Hyp` — the two named hypotheses

The capstone of this tier carries exactly two hypotheses that are not
discharged here, and they are the two tiers this one does not own.  The
precedent is the original campaign's `conron.model_exists`
(`proof/ConRon/RefineOld/Main.lean:174`), which carried `hk` and `hind` in the
same position for the same reason.

**`CoreSpec F` — the CORE tier's.**  Its main field is **`Bridge/Core/
Knot.lean`'s own `KnotSpec`**, taken as written: the six slots of
`ConRon.Arena.coreKnot .verified false fe id f` against con-leche's six fueled entry
points, at `CheckOK`/`Ext` with the `SimE`/`SimV` answer relations and the
`Expr.WScoped d e` precondition.  Nothing of it is restated here —
`Bridge/Core/Induction.lean`'s `knot_spec_checkFuel` is what discharges it, and
`CoreSpec.of_knot` below does that in one line.

**Two things `CoreSpec` adds, and why.**

1. **It quantifies over `env` and `fe`.**  `Bridge/Core`'s `knot_spec` fixes
   one environment; the FOLD's environment changes at every declaration.  Its
   `EnvWF env` hypothesis is `knot_spec`'s `henv`, which is why `FoldOK`
   (`Bridge/Checker/Inv.lean`) carries `EnvWF` as a clause — con-leche's own
   join point (`Verify/Cached/BridgeC.lean:609`) carries it too.
2. **`ensureSortCore` is not a slot of `coreKnot`.**  `Arena/Core.lean` builds
   it on top (`ensureSort (pureFnsA .verified false fe fuel) fe depth e`) and the
   declaration front door calls it at every constant, so `EnsureSortSpec` is a
   second field, in `Bridge/Core/Knot.lean`'s `BodySpec` shape.  It is one
   `whnf` call and a tag test, and `Bridge/Core/EnsureSort.lean` discharges
   it.

**What the Core tier's frame does not say, and this tier needs.**
`KnotSpec`'s postcondition is `CheckOK false env fe s' ∧ Ext s₀.store s'.store`.
`CheckOK` carries `PinsOK s'`, so the pin table still DENOTES — but the fold
also needs `PersPins s'` (the pin handles are persistent), and that is
transported by `s'.pins = s₀.pins` and nothing else.  No core entry writes
`s.pins`, so the clause is free; `CoreStep` below carries it, and every slot
of `KnotSpec` and `EnsureSortSpec` ends `s'.pins = s₀.pins`, which is what
lets the run-form proofs of `Bridge/Checker/Base.lean` and
`Bridge/Checker/Arms.lean` conclude `CoreStep` at all.

**`IndSpec` — the INDUCTIVES tier's**.  `checkDecl`'s `.indDecl` arm, past
the pin recogniser (`checkIndRoute` below: the declared parameter count, then
`checkBlock` on every block `blockParts?` reads and `checkShapeless` on the
rest), has the whole of `Arena/Inductives/**` under it, and the arm is the
single place the declaration checker reaches it.  So the whole inductive
install is one hypothesis, exactly as `RefineOld/Main.lean`'s
`hind : IndRoutesSpec .Verified` was.
-/
module

public import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Core.Induction
import ConRon.Bridge.Core.EnsureSort
public import ConRon.Arena.CheckDecl
public import ConRon.Bridge.Core.Knot
public import ConLeche.Kernel.CheckDecl

public section

open ConLeche ConRon.Arena Std.WP
open scoped Lean.Order

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## What a core call leaves behind

Every clause of the Core tier's `KnotSpec` has the same frame: the invariant
survives at the SAME environment (a core call never installs) and the arena
only grows.  `CoreStep` is that frame plus the pin-table equation the module
note explains. -/

/-- con-leche: ConLeche/Verify/Cached/SimC.lean:366 SimC — what a core entry
point leaves behind: the invariant at the same environment, an append, and an
untouched pin table. -/
structure CoreStep (env : Env) (fe : IFEnv) (s s' : AState) :
    Prop where
  ok : CheckOK false env fe s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins

theorem CoreStep.refl {env : Env} {fe : IFEnv} {s : AState}
    (h : CheckOK false env fe s) : CoreStep env fe s s :=
  ⟨h, Ext.refl _, rfl⟩

theorem CoreStep.trans {env : Env} {fe : IFEnv} {a b c : AState}
    (h₁ : CoreStep env fe a b) (h₂ : CoreStep env fe b c) :
    CoreStep env fe a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, by rw [h₂.pins, h₁.pins]⟩

/-! ## The overlay's inverse

The Rust keeps ONE environment index and runs `checkDecl`'s structural-`Nat`
gate at the index with the definition pushed, then pops it again
(`IFEnv.popTemp`, con-leche's `FEnv.overlay`).  Nothing in the invariant reads
an index except through `find?` and the raw table lookup (`IFEnvOK`'s
clauses; `CacheOK` and `PinsOK` do not mention it), so the invariant at `fe` IS
the invariant at any index answering `fe`'s lookups. -/

/-- con-leche: none — a push popped puts the own index back as it was, row for row. -/
theorem IFEnv.idx_popTemp (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) :
    ((fe.push ci).popTemp ci.name fe.idx[ci.name]?).idx[n]? = fe.idx[n]? := by
  simp only [IFEnv.popTemp, IFEnv.push]
  cases hp : fe.idx[ci.name]? with
  | some r =>
    simp only [Std.HashMap.getElem?_insert]
    by_cases hb : (ci.name == n) = true
    · obtain rfl : ci.name = n := by simpa using hb
      simp [hp]
    · simp [hb]
  | none =>
    simp only [Std.HashMap.getElem?_erase, Std.HashMap.getElem?_insert]
    by_cases hb : (ci.name == n) = true
    · obtain rfl : ci.name = n := by simpa using hb
      simp [hp]
    · simp [hb]

/-- con-leche: none — **a push popped answers the old `find?`**. -/
theorem IFEnv.find?_popTemp (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) :
    ((fe.push ci).popTemp ci.name fe.idx[ci.name]?).find? n = fe.find? n := by
  rw [IFEnv.find?_eq, IFEnv.find?_eq, IFEnv.idx_popTemp]
  rfl

/-- con-leche: none — `IFEnvOK` reads its index through `find?` and the raw
table lookup only. -/
theorem IFEnvOK.congr_lookup {env : Env} {fe fe' : IFEnv} {s : AState}
    (h : IFEnvOK env fe s) (hf : ∀ n, fe'.find? n = fe.find? n)
    (ht : ∀ n, fe'.rawTable? n = fe.rawTable? n) :
    IFEnvOK env fe' s :=
  have hT : ∀ n, fe'.findTable? n = fe.findTable? n := fun n => by
    simp only [IFEnv.findTable?, hf, ht]
  { hit := fun n ci hn => h.hit n ci (by rw [← hf]; exact hn)
    cover := fun nm c he => by
      obtain ⟨n, ci, hd, hfn, hc⟩ := h.cover nm c he
      exact ⟨n, ci, hd, by rw [hf]; exact hfn, hc⟩
    tblHit := fun n t hn => h.tblHit n t (by rw [← hT]; exact hn)
    tblCover := fun nm pt he => by
      obtain ⟨n, t, hd, hfn, hc⟩ := h.tblCover nm pt he
      exact ⟨n, t, hd, by rw [hT]; exact hfn, hc⟩ }

/-- con-leche: none — `IFEnvOK.congr_lookup` at the same table map. -/
theorem IFEnvOK.congr_find {env : Env} {fe fe' : IFEnv} {s : AState}
    (h : IFEnvOK env fe s) (hf : ∀ n, fe'.find? n = fe.find? n)
    (ht : fe'.tbls = fe.tbls) (hb : fe'.base = fe.base) :
    IFEnvOK env fe' s :=
  h.congr_lookup hf fun n => by simp only [IFEnv.rawTable?, ht, hb]

/-- con-leche: none — so does the whole checker invariant. -/
theorem CheckOK.congr_find {env : Env} {fe fe' : IFEnv}
    {s : AState} (h : CheckOK false env fe s) (hf : ∀ n, fe'.find? n = fe.find? n)
    (ht : fe'.tbls = fe.tbls) (hb : fe'.base = fe.base) :
    CheckOK false env fe' s :=
  ⟨h.state, h.caches, h.pins, h.ienv.congr_find hf ht hb⟩

/-- con-leche: none — and so does a core step's frame. -/
theorem CoreStep.congr_find {env : Env} {fe fe' : IFEnv}
    {s s' : AState} (h : CoreStep env fe s s')
    (hf : ∀ n, fe'.find? n = fe.find? n) (ht : fe'.tbls = fe.tbls)
    (hb : fe'.base = fe.base) :
    CoreStep env fe' s s' :=
  ⟨h.ok.congr_find hf ht hb, h.ext, h.pins⟩

/-- con-leche: none — **a name the environment lacks, the index lacks**:
`IFEnvOK.hit`'s contrapositive at a handle that denotes it. -/
theorem IFEnvOK.find?_none {env : Env} {fe : IFEnv} {s : AState}
    (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) (he : env.find? nm = none) :
    fe.find? n = none := by
  cases hf : fe.find? n with
  | none => rfl
  | some ci =>
    obtain ⟨nm', c, hd', -, he'⟩ := h.hit n ci hf
    rw [hd] at hd'
    obtain rfl := Option.some.inj hd'
    rw [he] at he'
    exact absurd he' (by simp)

/-! ## The seventh entry point -/

/-- con-leche: none — the LEVEL-valued answer relation, for `ensureSort`.
`Bridge/Core/Knot.lean`'s `SimE` at a `Level` answer; no well-scopedness
conjunct, because a level has no binder depth. -/
@[expose] def SimL (op : Nat → Nat → Expr → CheckM Level) (d : Nat) (e : Expr)
    (st' : EStore) (r : LIdx) : Prop :=
  ∃ u, denoteL st'.ls r = some u ∧ ∃ F, op F d e = .ok u

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore — **the
seventh entry point, which is not a slot**.  `Bridge/Core/Knot.lean`'s
six-field `KnotSpec` does not cover it because `coreKnot` does not have it;
the declaration front door calls it at every constant, so this tier needs it.

Stated in `BodySpec`'s shape — a `Std.WP` triple — like everything else the
Core tier owns. -/
@[expose] def EnsureSortSpec (env : Env) (fe : IFEnv) (f : Nat) :
    Prop :=
  ∀ (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr),
    CheckOK false env fe s₀ → denoteE s₀.store i = some e →
    Expr.WScoped d e →
    ⦃fun s => s = s₀⦄ Arena.ensureSortCore .verified fe f d i
    ⦃fun r s' => CheckOK false env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimL (ConLeche.ensureSortCore .verified false env) d e s'.store r; ⊤⦄

/-! ## The Core tier's theorem, as this tier uses it -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC — **THE CORE
TIER'S THEOREM, as this tier's hypothesis**: `Bridge/Core/Knot.lean`'s
`KnotSpec` at EVERY well-formed environment and its index, plus the seventh
entry point.

The quantification is the fold's: its environment changes at every
declaration while `Bridge/Core/Induction.lean`'s `knot_spec` fixes one. -/
structure CoreSpec (f : Nat) : Prop where
  knot : ∀ (env : Env) (fe : IFEnv), EnvWF env → Core.KnotSpec false env fe f
  sort : ∀ (env : Env) (fe : IFEnv), EnvWF env → EnsureSortSpec env fe f

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC — **the Core
tier's half, discharged**: `Bridge/Core/Induction.lean`'s
`knot_spec_checkFuel` IS the `knot` field, so what the capstone still owes the
Core tier is `EnsureSortSpec` and nothing else.

The Core tier's statement and this tier's hypothesis are the same statement,
and one line joins them. -/
theorem CoreSpec.of_knot (hs : ∀ (env : Env) (fe : IFEnv), EnvWF env →
      EnsureSortSpec env fe Arena.checkFuel) :
    CoreSpec Arena.checkFuel :=
  ⟨fun _ _ henv => Core.knot_spec_checkFuel henv, hs⟩

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore — **the
seventh entry point, discharged**: `Bridge/Core/EnsureSort.lean`'s
`ensureSortCore_spec` IS this statement.  `SimL` there and `SimL` here are the
same definition, which is why this is one term. -/
theorem ensureSortSpec_of_knot {env : Env} {fe : IFEnv}
    {f : Nat} (hsim : Core.KnotSpec false env fe f) :
    EnsureSortSpec env fe f :=
  fun s₀ d i e hok hden hw => Core.ensureSortCore_spec hsim s₀ d i e hok hden hw

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC — **`CoreSpec`
with NOTHING left to supply**: both fields come from `Bridge/Core`, so the
capstone's Core-tier hypothesis is discharged outright. -/
theorem CoreSpec.of_core :
    CoreSpec Arena.checkFuel :=
  CoreSpec.of_knot
    (fun _ _ henv => ensureSortSpec_of_knot (Core.knot_spec_checkFuel henv))

/-! ## The inductive install -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:163-182 checkDecl (the
`.indDecl` arm past `basisNameHit`) — **the unpinned inductive route, named**:
`Arena/CheckDecl.lean`'s `checkDecl` arm after the pin recogniser declined,
verbatim: con-leche's uniform inductive route.  `checkDecl`'s `.indDecl` arm
unfolds to it by `rfl`. -/
@[expose] def checkIndRoute (fe : IFEnv) (block : List IConstantInfo)
    (nP : Nat) : AM IFEnv := do
  if !(← indParamsOk nP block) then
    fail (.invalid "number of parameters mismatch")
  else
    match ← blockShape? nP block with
    | some p => checkBlock .verified fe block p
    | none => checkShapeless .verified fe block

/-- con-leche: ConLeche/Semantics/Bridge/Sound.lean:38 checkShapeless_ne_ok —
**a block the recogniser does not read never installs**: the twin's
`checkShapeless` ends in a decline whatever its formers' checks do. -/
theorem checkShapeless_ne_ok {mode : CheckMode} {fe fe' : IFEnv}
    {block : List IConstantInfo} {s s' : AState} :
    checkShapeless mode fe block s ≠ .ok (fe', s') := by
  intro h
  unfold ConRon.Arena.checkShapeless at h
  obtain ⟨_, s1, _, h2⟩ := AM.bind_ok h
  exact nomatch h2

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:163-182 checkDecl (the `.indDecl`
arm) — **THE INDUCTIVES TIER'S THEOREM, as this tier's hypothesis**.

The hypothesis `hpin` is the arena's own dispatch, already taken: this clause
covers the route `basisNameHit` did NOT recognise, which is the one
`checkIndRoute` runs.  The recogniser's own exactness is
`Bridge/Checker/Basis.lean`'s and is not part of this hypothesis.

What the route's environment becomes is not a clause: con-leche's `checkDecl`
pushes what the declaration says (`Bridge/Checker/Pushes.lean`), the job's
environment is dropped with its scratch tier, and the next record checks at
its own view of the stream's index.  No fold theorem reads `IndSpec`; they pass
it down to `checkDecl_bridge_ind`, and `Bridge/Inductives/Decl.lean`'s
`indSpec_of_bridge` discharges it. -/
structure IndSpec : Prop where
  run : ∀ {env : Env} {fe fe' : IFEnv} {s s' : AState}
      {block : List IConstantInfo} {b : List ConstantInfo} {nP : Nat}
      {pinsP : List NatOpPinSet},
    FoldOK env fe s → Frontend.denoteCIList s.store block = some b →
    ConLeche.basisNameHit b = none →
    checkIndRoute fe block nP s = .ok (fe', s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ env' F,
        ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env (.indDecl b nP)
          = .ok env'

end ConRon.Bridge
