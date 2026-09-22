/-
# `ConRon.Bridge.Checker.Hyp` — the two named hypotheses

The capstone of this tier carries exactly two hypotheses that are not
discharged here, and they are the two tiers this one does not own.  The
precedent is the original campaign's `conron.model_exists`
(`proof/ConRon/RefineOld/Main.lean:174`), which carried `hk` and `hind` in the
same position for the same reason.

**`CoreSpec μ F` — the CORE tier's** (`Bridge/Core/**`, task #97-P3-Core).
Its main field is `KnotSpec`, and **`KnotSpec` below is P3-Core's own
statement, field for field**, at the branch `p3-core` (`Bridge/Core/Knot.lean`,
`structure KnotSpec (mode : CheckMode) (env : Env) (fe : IFEnv) (f : Nat)`):
the same six slots of `ConRon.Arena.coreKnot mode fe id f`, the same
`CheckOK`/`Ext` frame, the same `SimE`/`SimV` answer relations with the pure
side's fuel existential and the answer's well-scopedness folded in, and the
same `Expr.WScoped d e` precondition.

**One difference, and it is deliberate: the RUN form.**  P3-Core states each
slot as a `Std.Do` triple, because its arms are written with `mvcgen`.  This
tier states them as runs (`… s₀ = .ok (r, s')`), because its proofs are
`AM.bind_ok` inversions and never call `mvcgen`.  The two are one
`Bridge/Rel.lean`-`AM.of_run` apart, so **the merge's adapter is six lines**,
one per slot, and neither statement has to change.

**Two additions the Core round does not cover.**

1. `ensureSortCore` is NOT a slot of `coreKnot` — `Arena/Core.lean` builds it
   on top (`ensureSort (pureFnsA mode fe fuel) fe depth e`) — but the
   declaration front door calls it at every constant.  So it is a second
   field, `EnsureSortSpec`, at the same frame.
2. `CoreSpec` quantifies over `env` and `fe`, because the FOLD's environment
   changes at every declaration while P3-Core's `knot_spec` fixes one.  Its
   `EnvWF env` hypothesis is P3-Core's `henv`, and it is why `FoldOK`
   (`Bridge/Checker/Inv.lean`) carries `EnvWF` as a clause.

**`IndSpec μ` — the INDUCTIVES tier's**.  `Arena/Inductives.lean`'s
`checkIndDecl` is 9 500 lines of arena twin under it, and `checkDecl`'s
`.indDecl` arm is the single place the declaration checker calls it.  So the
whole inductive install is one hypothesis, exactly as
`RefineOld/Main.lean`'s `hind : IndRoutesSpec .Verified` was.
-/
import ConRon.Bridge.Checker.Inv
import ConLeche.Verify.Shift

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## What a core call leaves behind

Every clause of `KnotSpec` has the same frame: the invariant survives at the
SAME environment (a core call never installs), the arena only grows, and the
pin table is untouched.  One structure, so a caller composes with one
`trans`.

P3-Core's frame is `CheckOK mode env fe s' ∧ Ext s₀.store s'.store`; the pin
clause is this tier's addition and it is free (no core entry writes
`s.pins`), because `PinsOK` has to survive the NEXT `dropScratch` and
`PinsOK.pmono` needs it. -/

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

/-! ## The answer relations

`Bridge/Core/Knot.lean`'s `SimE` and `SimV`, verbatim.  Restated rather than
imported because `Bridge/Core/**` is a concurrent round; at the merge one of
the two copies goes and nothing else changes. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the handle-valued answer
relation of a core entry point: the answer handle denotes a well-scoped `v`
that con-leche's own fueled operation produces at some fuel. -/
def SimE (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (e : Expr)
    (st' : EStore) (r : EIdx) : Prop :=
  ∃ v, denoteE st' r = some v ∧ Expr.WScoped d v ∧ ∃ F, op F d e = .ok v

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — the `Bool`-valued answer
relation, for the `defeq` slot. -/
def SimV (op : Nat → Nat → Expr → Expr → CheckM Bool) (d : Nat)
    (a b : Expr) (x : Bool) : Prop :=
  ∃ F, op F d a b = .ok x

/-- con-leche: none — the LEVEL-valued answer relation, for `ensureSort`
(which `coreKnot` does not have a slot for). -/
def SimL (op : Nat → Nat → Expr → CheckM Level) (d : Nat) (e : Expr)
    (st' : EStore) (r : LIdx) : Prop :=
  ∃ u, denoteL st'.ls r = some u ∧ ∃ F, op F d e = .ok u

theorem SimE.ext {op : Nat → Nat → Expr → CheckM Expr} {d : Nat} {e : Expr}
    {st st' : EStore} {r : EIdx} (h : SimE op d e st r) (hx : Ext st st') :
    SimE op d e st' r := by
  obtain ⟨v, hv, hw, F, hF⟩ := h
  exact ⟨v, hx.expr _ _ hv, hw, F, hF⟩

theorem SimL.ext {op : Nat → Nat → Expr → CheckM Level} {d : Nat} {e : Expr}
    {st st' : EStore} {r : LIdx} (h : SimL op d e st r) (hx : Ext st st') :
    SimL op d e st' r := by
  obtain ⟨u, hu, F, hF⟩ := h
  exact ⟨u, hx.lss.ls.lvl _ _ hu, F, hF⟩

/-! ## The core knot -/

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:34 SSimC
con-leche: ConLeche/Verify/SimIKnot.lean:28 SSimI
**THE CORE TIER'S THEOREM, as this tier's hypothesis** —
`Bridge/Core/Knot.lean`'s `KnotSpec` in the run form (module note), at the six
slots of `ConRon.Arena.coreKnot mode fe id f`.

Each clause reads: *from the state invariant, a subject that denotes and is
well scoped at the query's depth, an accepting arena run gives an accepting
pure run at SOME fuel whose answer the arena's answer denotes.*  Nothing is
claimed of a rejecting run — a `native` decline claims nothing at all (DESIGN
§8.3) — so the bridge is a refinement, which is what
`checkDeclsPure_sound_of` consumes (the history report's fine print 1). -/
structure KnotSpec (mode : CheckMode) (env : Env) (fe : IFEnv) (f : Nat) :
    Prop where
  /-- Head normalization without delta. -/
  whnfCore : ∀ {s₀ s' : AState} {d : Nat} {i r : EIdx} {e : Expr},
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e → Expr.WScoped d e →
    (coreKnot mode fe id f).whnfCore d i s₀ = .ok (r, s') →
    CoreStep mode env fe s₀ s' ∧ SimE (ConLeche.whnfCore mode env) d e s'.store r
  /-- The full reduction loop. -/
  whnf : ∀ {s₀ s' : AState} {d : Nat} {i r : EIdx} {e : Expr},
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e → Expr.WScoped d e →
    (coreKnot mode fe id f).whnf d i s₀ = .ok (r, s') →
    CoreStep mode env fe s₀ s' ∧ SimE (ConLeche.whnf mode env) d e s'.store r
  /-- Full-grade type inference. -/
  infer : ∀ {s₀ s' : AState} {d : Nat} {i r : EIdx} {e : Expr},
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e → Expr.WScoped d e →
    (coreKnot mode fe id f).infer d i s₀ = .ok (r, s') →
    CoreStep mode env fe s₀ s' ∧
      SimE (ConLeche.inferTypeCore mode env) d e s'.store r
  /-- Definitional equality, at the ORDERED pair the memo is keyed by. -/
  defeq : ∀ {s₀ s' : AState} {d : Nat} {i j : EIdx} {a b : Expr} {x : Bool},
    CheckOK mode env fe s₀ → denoteE s₀.store i = some a →
    denoteE s₀.store j = some b → Expr.WScoped d a → Expr.WScoped d b →
    (coreKnot mode fe id f).defeq d i j s₀ = .ok (x, s') →
    CoreStep mode env fe s₀ s' ∧ SimV (ConLeche.isDefEqCore mode env) d a b x
  /-- The annotation pass. -/
  annotate : ∀ {s₀ s' : AState} {d : Nat} {i r : EIdx} {e : Expr},
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e → Expr.WScoped d e →
    (coreKnot mode fe id f).annotate d i s₀ = .ok (r, s') →
    CoreStep mode env fe s₀ s' ∧
      SimE (ConLeche.annotateCore mode env) d e s'.store r
  /-- The io grade (con-leche's task #170): its own body, its own table. -/
  inferIO : ∀ {s₀ s' : AState} {d : Nat} {i r : EIdx} {e : Expr},
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e → Expr.WScoped d e →
    (coreKnot mode fe id f).inferIO d i s₀ = .ok (r, s') →
    CoreStep mode env fe s₀ s' ∧
      SimE (ConLeche.inferTypeIO mode env) d e s'.store r

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore — **the
seventh entry point, which is not a slot**.  `Arena/Core.lean` builds
`ensureSortCore` on top of the knot (`ensureSort (pureFnsA mode fe fuel) fe
depth e`), so `Bridge/Core/Knot.lean`'s six-field record does not cover it;
the declaration front door calls it at every constant, so this tier needs it.

It is one `whnf` call and a tag test, so discharging it from `KnotSpec.whnf`
is a short proof — but it is the Core tier's to write, not this one's. -/
structure EnsureSortSpec (mode : CheckMode) (env : Env) (fe : IFEnv) (f : Nat) :
    Prop where
  ensureSort : ∀ {s₀ s' : AState} {d : Nat} {i : EIdx} {r : LIdx} {e : Expr},
    CheckOK mode env fe s₀ → denoteE s₀.store i = some e → Expr.WScoped d e →
    Arena.ensureSortCore mode fe f d i s₀ = .ok (r, s') →
    CoreStep mode env fe s₀ s' ∧
      SimL (ConLeche.ensureSortCore mode env) d e s'.store r

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC — **the Core
tier's theorem as this tier uses it**: at EVERY well-formed environment and
its index, because the fold's environment changes at every declaration while
P3-Core's `knot_spec` fixes one.

`EnvWF env` is P3-Core's `henv`, and `FoldOK` carries it for exactly this
reason. -/
structure CoreSpec (mode : CheckMode) (f : Nat) : Prop where
  knot : ∀ (env : Env) (fe : IFEnv), EnvWF env → KnotSpec mode env fe f
  sort : ∀ (env : Env) (fe : IFEnv), EnvWF env → EnsureSortSpec mode env fe f

/-! ## The inductive install -/

/-- con-leche: ConLeche/Kernel/Checker.lean:440-609 checkDecl (the `.indDecl`
arm) — **THE INDUCTIVES TIER'S THEOREM, as this tier's hypothesis**.

The hypothesis `hpin` is the arena's own dispatch, already taken: this clause
covers the route `basisPinHit` did NOT recognise, which is the one
`Inductives.checkIndDecl` runs.  The recogniser's own exactness is
`Bridge/Checker/Basis.lean`'s and is not part of this hypothesis.

The precedent is `RefineOld/Main.lean`'s `hind : IndRoutesSpec .Verified`:
one named hypothesis for the whole inductive install, discharged by a tier of
its own. -/
structure IndSpec (μ : CheckMode) : Prop where
  run : ∀ {env : Env} {fe fe' : IFEnv} {s s' : AState}
      {block : List IConstantInfo} {b : List ConstantInfo} {nP : Nat}
      {pinsP : List NatOpPinSet},
    FoldOK μ env fe s → Frontend.denoteCIList s.store block = some b →
    ConLeche.basisPinHit b = none →
    Inductives.checkIndDecl μ fe block nP s = .ok (fe', s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      PersIFEnv fe' ∧ IFEnvCoh fe' ∧ fe.visibleBelow ≤ fe'.visibleBelow ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
        ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.indDecl b nP)
          = .ok env'

end ConRon.Bridge
