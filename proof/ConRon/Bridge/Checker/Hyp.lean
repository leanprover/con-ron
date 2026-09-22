/-
# `ConRon.Bridge.Checker.Hyp` — the two named hypotheses

The capstone of this tier carries exactly two hypotheses that are not
discharged here, and they are the two tiers this one does not own.  The
precedent is the original campaign's `conron.model_exists`
(`proof/ConRon/RefineOld/Main.lean:174`), which carried `hk` and `hind` in the
same position for the same reason.

**`KnotSpec μ F` — the CORE tier's** (`Bridge/Core/**`, task #97-P3-Core).
The seven fueled entry points of `Arena/Core.lean` simulate con-leche's
`ConLeche/Kernel/TypeChecker.lean` at the same fuel, over `CheckOK`.  This is
the shape the coordinator's brief fixes: *"its `knot_spec : ∀ f, KnotSpec f`
is YOUR hypothesis"*.  Stated here, to be IDENTIFIED with `Bridge/Core`'s at
the merge — the two must agree clause for clause, and if they do not, the
merge's job is to say which is right and adjust this one.

**`IndSpec μ` — the INDUCTIVES tier's**.  `Arena/Inductives.lean`'s
`checkIndDecl` is 9 500 lines of arena twin under it, and `checkDecl`'s
`.indDecl` arm is the single place the declaration checker calls it.  So the
whole inductive install is one hypothesis, exactly as
`RefineOld/Main.lean`'s `hind : IndRoutesSpec .Verified` was.

Both are stated at the DENOTATION, so neither mentions a handle type in its
conclusion: what a discharging tier proves is that the arena's answer denotes
con-leche's answer, which is the only thing `ConLeche.checkDecl`'s statement
can consume.
-/
import ConRon.Bridge.Checker.Inv

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## What a core call leaves behind

Every clause of `KnotSpec` has the same frame: the invariant survives at the
SAME environment (a core call never installs), the arena only grows, and the
pin table is untouched.  One structure, so a caller composes with one
`trans`. -/

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

/-! ## The core knot -/

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:23-58 pureFns — **THE CORE
TIER'S THEOREM, as this tier's hypothesis**: the seven fueled entry points of
`Arena/Core.lean` simulate `ConLeche/Kernel/TypeChecker.lean`'s at the same
mode, environment, fuel and depth.

Each clause reads: *from the state invariant, an accepting arena run gives an
accepting pure run whose answer the arena's answer denotes.*  Nothing is
claimed of a rejecting run — a `native` decline claims nothing at all (DESIGN
§8.3) — so the bridge is a refinement, which is exactly what
`checkDeclsPure_sound_of` consumes (the history report's fine print 1).

To be identified with `ConRon.Bridge.Core`'s statement at the merge (module
note). -/
structure KnotSpec (μ : CheckMode) (F : Nat) : Prop where
  whnfCore : ∀ {env : Env} {fe : IFEnv} {s s' : AState} {d : Nat} {h r : EIdx},
    CheckOK μ env fe s → Arena.whnfCore μ fe F d h s = .ok (r, s') →
    CoreStep μ env fe s s' ∧ ∀ e, denoteE s.store h = some e →
      ∃ b, ConLeche.whnfCore μ env F d e = .ok b ∧ denoteE s'.store r = some b
  whnf : ∀ {env : Env} {fe : IFEnv} {s s' : AState} {d : Nat} {h r : EIdx},
    CheckOK μ env fe s → Arena.whnf μ fe F d h s = .ok (r, s') →
    CoreStep μ env fe s s' ∧ ∀ e, denoteE s.store h = some e →
      ∃ b, ConLeche.whnf μ env F d e = .ok b ∧ denoteE s'.store r = some b
  inferTypeCore : ∀ {env : Env} {fe : IFEnv} {s s' : AState} {d : Nat} {h r : EIdx},
    CheckOK μ env fe s → Arena.inferTypeCore μ fe F d h s = .ok (r, s') →
    CoreStep μ env fe s s' ∧ ∀ e, denoteE s.store h = some e →
      ∃ b, ConLeche.inferTypeCore μ env F d e = .ok b ∧ denoteE s'.store r = some b
  inferTypeIO : ∀ {env : Env} {fe : IFEnv} {s s' : AState} {d : Nat} {h r : EIdx},
    CheckOK μ env fe s → Arena.inferTypeIO μ fe F d h s = .ok (r, s') →
    CoreStep μ env fe s s' ∧ ∀ e, denoteE s.store h = some e →
      ∃ b, ConLeche.inferTypeIO μ env F d e = .ok b ∧ denoteE s'.store r = some b
  annotateCore : ∀ {env : Env} {fe : IFEnv} {s s' : AState} {d : Nat} {h r : EIdx},
    CheckOK μ env fe s → Arena.annotateCore μ fe F d h s = .ok (r, s') →
    CoreStep μ env fe s s' ∧ ∀ e, denoteE s.store h = some e →
      ∃ b, ConLeche.annotateCore μ env F d e = .ok b ∧ denoteE s'.store r = some b
  isDefEqCore : ∀ {env : Env} {fe : IFEnv} {s s' : AState} {d : Nat} {a b : EIdx}
      {r : Bool},
    CheckOK μ env fe s → Arena.isDefEqCore μ fe F d a b s = .ok (r, s') →
    CoreStep μ env fe s s' ∧ ∀ x y, denoteE s.store a = some x →
      denoteE s.store b = some y → ConLeche.isDefEqCore μ env F d x y = .ok r
  ensureSortCore : ∀ {env : Env} {fe : IFEnv} {s s' : AState} {d : Nat} {h : EIdx}
      {r : LIdx},
    CheckOK μ env fe s → Arena.ensureSortCore μ fe F d h s = .ok (r, s') →
    CoreStep μ env fe s s' ∧ ∀ e, denoteE s.store h = some e →
      ∃ u, ConLeche.ensureSortCore μ env F d e = .ok u ∧
        denoteL s'.store.ls r = some u

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
