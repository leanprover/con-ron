/-
# `ConRon.Bridge.Checker.Arms` — `checkDecl`'s seven arms, PROVED

`Bridge/Checker/Decl.lean` states what an arm concludes (`DeclOut`) and what
relates the two pin lists (`PinsDenote`); this module is the seven arms
themselves, and every one of them is an ASSEMBLY — a chain of `AM.bind_ok`
inversions over statements that live one tier down, closed by a pure step
lemma about con-leche's own `checkDecl` clause.

**Why the arms are not in `Decl.lean`** (task #97-P3-Checker-2).  An arm's
content is `Bridge/Checker/Base.lean`'s `checkConstantVal_bridge`,
`Bridge/Checker/DeclVal.lean`'s three value checks and two pin gates, and
`Bridge/Checker/Basis.lean`'s recognisers and installs — and all three of
those modules import `Decl.lean` for `DeclOut` and `PinsDenote`.  Proving the
arms in `Decl.lean` would close a cycle; proving them here does not, and the
one consumer (`Bridge/Checker/Fold.lean`'s `Arena.checkDecl_bridge`) simply
imports this module beside `Mono.lean`.

## The shape of every arm

    simp only [Arena.checkDecl] at hrun      -- the twin's own clause
    ⟨…⟩ := AM.bind_ok hrun                   -- one per monadic step
    ⟨…⟩ := <the step's bridge theorem>       -- one per step
    ⟨…⟩ := AM.dguard_ok / AM.ite_ok          -- one per guard
    exact ⟨…, <the pure step lemma>⟩         -- con-leche's own clause

The `FoldOK` that each step after the first needs is rebuilt from the previous
step's `CoreStep`/`Ext` by `denoteFEnv_pext` and `PersPins.mono`; that
bookkeeping is `FoldOK.step` below, which is the only thing in this module
that is not a transcription.
-/
import ConRon.Bridge.Checker.DeclVal
import ConRon.Bridge.Checker.Basis

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## Carrying the fold's invariant across a step

A step of an arm leaves `CheckOK` at the SAME environment and an `Ext`; the
other four clauses of `FoldOK` are about the environment index and the pin
handles, and both transport. -/

/-- con-leche: none — `FoldOK` survives a step that only appends and leaves
the environment alone. -/
theorem FoldOK.step {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (h : FoldOK μ env fe s) (hck : CheckOK μ env fe s')
    (hx : Ext s.store s'.store) (hp : s'.pins = s.pins) :
    FoldOK μ env fe s' where
  check := hck
  envWF := h.envWF
  persPins := h.persPins.mono hp
  persEnv := h.persEnv
  coh := h.coh
  denote := denoteFEnv_pext (PExt.of_ext hx) h.persEnv h.denote

/-- con-leche: none — the same at a `CoreStep`, which is what every core
consumer hands back. -/
theorem FoldOK.ofCore {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (h : FoldOK μ env fe s) (hc : CoreStep μ env fe s s') :
    FoldOK μ env fe s' := h.step hc.ok hc.ext hc.pins

/-! ## The pure side's step lemmas

Task #97-P3-Core §5's rule 8: one lemma per CLAUSE of con-leche's `checkDecl`,
stated in the shape the arm's last tactic produces. -/

/-- con-leche: ConLeche/Kernel/Checker.lean:486-489 checkDecl (the `.thmDecl`
arm). -/
theorem checkDecl_thm_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env' : Env} {c cA : ConstantVal} {x : Expr}
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA)
    (h2 : ConLeche.checkThmVal (ConLeche.fueledOps μ F) env cA x = .ok env') :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.thmDecl c x)
      = .ok env' := by
  simp only [ConLeche.checkDecl, h1, h2, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Checker.lean:562 checkDecl (the `.basisDecl`
arm). -/
theorem checkDecl_basis_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env' : Env} {kind : BasisKind}
    (h : ConLeche.checkBasisDecl (m := CheckM) env kind = .ok env') :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.basisDecl kind)
      = .ok env' := by
  simp only [ConLeche.checkDecl]; exact h

/-- con-leche: ConLeche/Kernel/Checker.lean:602-626 checkDecl (the `.quotDecl`
arm) at a MATCHING `.type` record: the pinned quotient block installs whole. -/
theorem checkDecl_quot_type_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env' : Env} {c : ConstantVal}
    (hhit : ConLeche.quotPinHit .type c = true)
    (h : ConLeche.checkBasisDecl (m := CheckM) env .quotK = .ok env') :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.quotDecl .type c)
      = .ok env' := by
  simp only [ConLeche.checkDecl, hhit, if_true]; exact h

/-- con-leche: ConLeche/Kernel/Checker.lean:602-626 checkDecl (the `.quotDecl`
arm) at a MATCHING record of any other kind: the block is already installed
and the record adds nothing. -/
theorem checkDecl_quot_other_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c : ConstantVal} {k : QuotKind}
    (hk : k ≠ .type) (hhit : ConLeche.quotPinHit k c = true) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.quotDecl k c)
      = .ok env := by
  cases k <;> simp only [ConLeche.checkDecl, hhit, if_true] <;> first
    | rfl
    | exact absurd rfl hk

/-! ## The pinned name LISTS

Three readers of the pin table, each a short chain of `pinAt`s that leaves the
state alone; the answer is `denoteNL` at con-leche's own list, and
`denoteNList_contains` turns each arm's `contains` test into con-leche's. -/

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:72-73 reduceOpNames. -/
theorem reduceOpNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : reduceOpNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.reduceOpNames := by
  simp only [Arena.reduceOpNames] at hr
  obtain ⟨h1, t1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.reduceNatName) hp rfl g1
  rw [e1] at r1
  obtain ⟨h2, t2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.reduceBoolName) hp rfl g2
  rw [e2] at r2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
  exact ⟨rfl, d1, d2, trivial⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:564-600 checkDecl (the `.indDecl`
arm) at a block the basis recogniser DID recognise: the pinned block installs
whole and the inductive route never runs. -/
theorem checkDecl_ind_basis_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env' : Env} {b : List ConstantInfo}
    {nP : Nat} {kind : BasisKind}
    (hhit : ConLeche.basisPinHit b = some kind)
    (h : ConLeche.checkBasisDecl (m := CheckM) env kind = .ok env') :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.indDecl b nP)
      = .ok env' := by
  simp only [ConLeche.checkDecl, hhit]; exact h

/-- con-leche: ConLeche/Kernel/Checker.lean:491-500 checkDecl (the
`.opaqueDecl` arm) with the compiler-trust gate NOT taken. -/
theorem checkDecl_opaque_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env2 : Env} {c cA : ConstantVal} {x : Expr}
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA)
    (h2 : ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env cA x = .ok env2)
    (h3 : ConLeche.reduceOpNames.contains cA.name = false) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.opaqueDecl c x)
      = .ok env2 := by
  simp only [ConLeche.checkDecl, h1, h2, h3, Bool.false_eq_true, if_false, bind,
    Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:491-500 checkDecl (the
`.opaqueDecl` arm) with the compiler-trust gate TAKEN. -/
theorem checkDecl_opaque_pin_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env2 : Env} {c cA : ConstantVal} {x : Expr}
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA)
    (h2 : ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env cA x = .ok env2)
    (h3 : ConLeche.reduceOpNames.contains cA.name = true)
    (h4 : ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 cA.name x
      = .ok ()) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.opaqueDecl c x)
      = .ok env2 := by
  simp only [ConLeche.checkDecl, h1, h2, h3, h4, if_true, bind, Except.bind,
    pure, Except.pure]

/-! ### The `.axiomDecl` arm's six exits -/

/-- con-leche: ConLeche/Kernel/Checker.lean:502-560 checkDecl — the
`Quot.sound` record: compared with the pinned block's fifth constant and
installing nothing. -/
theorem checkDecl_axiom_quotSound_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c : ConstantVal}
    (hnm : c.name = ConLeche.quotSoundName)
    (heq : ConLeche.ConstantInfo.canonEq (.axiomInfo c)
      (ConLeche.quotBasis.getD 4 (.axiomInfo default)) = true) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok env := by
  simp only [ConLeche.checkDecl, hnm, heq, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:502-560 checkDecl — a standard
axiom, installed. -/
theorem checkDecl_axiom_std_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c cA : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA)
    (h2 : ConLeche.stdAxiomOk env cA = true) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok ⟨.axiomInfo cA :: env.consts⟩ := by
  simp only [ConLeche.checkDecl, if_neg hnm, h1, h2, if_true, bind, Except.bind,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:502-560 checkDecl —
`Lean.trustCompiler`, installed. -/
theorem checkDecl_axiom_trust_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c cA : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA)
    (h2 : ConLeche.stdAxiomOk env cA = false)
    (h3 : cA.name = ConLeche.trustCompilerName)
    (h4 : ConLeche.trustCompilerOk env cA = true) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok ⟨.axiomInfo cA :: env.consts⟩ := by
  simp only [ConLeche.checkDecl, if_neg hnm, h1, h2, h3, h4, Bool.false_eq_true,
    if_false, if_true, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:502-560 checkDecl — an
`ofReduce*` axiom, installed. -/
theorem checkDecl_axiom_ofReduce_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c cA : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA)
    (h2 : ConLeche.stdAxiomOk env cA = false)
    (h3 : ¬ (cA.name = ConLeche.trustCompilerName))
    (h4 : cA.name = ConLeche.ofReduceNatName ∨
      cA.name = ConLeche.ofReduceBoolName)
    (h5 : ConLeche.ofReduceAxOk env cA = true) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok ⟨.axiomInfo cA :: env.consts⟩ := by
  simp only [ConLeche.checkDecl, if_neg hnm, h1, h2, h5, Bool.false_eq_true,
    if_false, if_true, if_neg h3, if_pos h4, bind, Except.bind, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:502-560 checkDecl — `sorryAx`, the
one axiom the checker tolerates as a DECLARATION: skipped, installing
nothing. -/
theorem checkDecl_axiom_sorryAx_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c cA : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA)
    (h2 : ConLeche.stdAxiomOk env cA = false)
    (h3 : ¬ (cA.name = ConLeche.trustCompilerName))
    (h4 : ¬ (cA.name = ConLeche.ofReduceNatName ∨
      cA.name = ConLeche.ofReduceBoolName))
    (h5 : ¬ (cA.name = ConLeche.propextName ∨ cA.name = ConLeche.choiceName))
    (h6 : cA.name = ConLeche.sorryAxName) :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok env := by
  simp only [ConLeche.checkDecl, if_neg hnm, h1, h2, Bool.false_eq_true,
    if_false, if_neg h3, if_neg h4, if_neg h5, if_pos h6, bind, Except.bind,
    pure, Except.pure]

/-! ## The seven arms -/

/-- con-leche: ConLeche/Kernel/Checker.lean:441-484 checkDecl (the `.defnDecl`
arm) — a definition, with the two `Nat`-operation pin gates behind it.

**The one arm of the seven still asserted**, and the only one whose
sub-statements were not all there: task #97-P3-Checker-2 wrote the five that
were missing (`Bridge/Checker/DeclVal.lean`'s `natOpNames_run`,
`natDivModNames_run`, `natOpDeps_run`, `natOpGuard_run`,
`natOpStoredOkAll_run`, `natOpEquations_run`, `substConst0Pairs_run`), so what
is left here is the assembly and nothing else.  It is the widest of the seven
to assemble because Lean's `do` elaborator copies the tail into both arms of
BOTH gates, so the four combinations — structural-`Nat` taken or not ×
`Nat.div`/`Nat.mod` taken or not — are four leaves, each needing its own pure
step lemma about con-leche's clause.

`sorry`: `checkConstantVal_bridge` → `checkDefnVal_bridge` → `natOpNames_run`
→ (`natOpGuard_run`, `natOpStoredOkAll_run`, `IFEnvOK`'s `hit` at
`fe2.find? cv.name`, `natOpEquations_run`, `substConst0Pairs_run`,
`certifyNatEqs_bridge`) → `natDivModNames_run` → `checkDivModPin_bridge`, and
the four pure step lemmas.  Task #97-P3-Checker's sorry list, item 7. -/
theorem checkDecl_bridge_defn {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {hint : ReducibilityHint} {c : ConstantVal} {x : Expr}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : Arena.checkDecl μ pins fe (.defnDecl cv value hint) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.defnDecl c x hint) s fe fe' s' := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:486-489 checkDecl (the `.thmDecl`
arm).

**PROVED** (task #97-P3-Checker-2): `checkConstantVal_bridge` and
`checkThmVal_bridge`, at one fuel. -/
theorem checkDecl_bridge_thm {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {c : ConstantVal} {x : Expr}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : Arena.checkDecl μ pins fe (.thmDecl cv value) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.thmDecl c x) s fe fe' s' := by
  simp only [Arena.checkDecl] at hrun
  obtain ⟨cvA, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, cA, F1, hcA, hpure1⟩ :=
    checkConstantVal_bridge hμ hk hok hcv g1
  have hok1 : FoldOK μ env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  obtain ⟨hstep2, hcoh2, hpush2, env', F2, hden2, hie2, hpure2⟩ :=
    checkThmVal_bridge hμ hk hok1 hcA hv1 r1
  have hle1 : F1 ≤ max F1 F2 := Nat.le_max_left _ _
  have hle2 : F2 ≤ max F1 F2 := Nat.le_max_right _ _
  exact
    { state := hstep2.ok.state
      ext := hstep1.ext.trans hstep2.ext
      pins := by rw [hstep2.pins, hstep1.pins]
      coh := hcoh2
      pushed := hpush2
      run := ⟨env', max F1 F2, hden2,
        checkDecl_thm_pure (checkConstantVal_mono hle1 hpure1)
          (checkThmVal_mono hle2 hpure2)⟩ }

/-- con-leche: ConLeche/Kernel/Checker.lean:491-500 checkDecl (the
`.opaqueDecl` arm), with the compiler-trust `reduce*` gate behind it.

**PROVED** (task #97-P3-Checker-2): the front door, the value check, and the
compiler-trust gate behind a `contains` test that `denoteNList_contains` makes
con-leche's. -/
theorem checkDecl_bridge_opaque {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {c : ConstantVal} {x : Expr}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : Arena.checkDecl μ pins fe (.opaqueDecl cv value) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.opaqueDecl c x) s fe fe' s' := by
  simp only [Arena.checkDecl] at hrun
  -- the front door
  obtain ⟨cvA, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, cA, F1, hcA, hpure1⟩ :=
    checkConstantVal_bridge hμ hk hok hcv g1
  have hok1 : FoldOK μ env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  -- the value check
  obtain ⟨fe2, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hstep2, hcoh2, hpush2, env2, F2, hden2, hie2, hpure2⟩ :=
    checkOpaqueVal_bridge hμ hk hok1 hcA hv1 g2
  have hx2 : Ext s1.store s2.store := hstep2.ext
  have hp2 : s2.pins = s1.pins := hstep2.pins
  have hst2 : StateOK s2 := hstep2.ok.state
  have hok2 : FoldOK μ env fe s2 := hok1.ofCore hstep2
  have hnm2 : denoteN s2.store.ns cvA.name = some cA.name :=
    denoteN_ext (denoteCV_inv hcA).1 hx2
  have hv2 : denoteE s2.store value = some x := denote_ext hv1 hx2
  -- the compiler-trust gate
  obtain ⟨ns, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨he3, hns⟩ := reduceOpNames_run hok2.check.pins g3
  rw [he3] at r3
  have hcont : ns.contains cvA.name = ConLeche.reduceOpNames.contains cA.name :=
    denoteNList_contains hst2.wf ns ConLeche.reduceOpNames
      (denoteNL_toList ns ConLeche.reduceOpNames (he3 ▸ hns)) cvA.name cA.name
      hnm2
  have hle1 : F1 ≤ max F1 F2 := Nat.le_max_left _ _
  have hle2 : F2 ≤ max F1 F2 := Nat.le_max_right _ _
  rcases AM.ite_ok r3 with ⟨hyes, hgood⟩ | ⟨hno, hgood⟩
  · -- the gate runs
    obtain ⟨u4, s4, g4, r4⟩ := AM.bind_ok hgood
    obtain ⟨hst4, hx4, hp4, F4, hpure4⟩ :=
      checkReducePin_bridge hμ hk hok2 hie2 hnm2 hv2 g4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
    have hle1' : F1 ≤ max (max F1 F2) F4 :=
      Nat.le_trans hle1 (Nat.le_max_left _ F4)
    have hle2' : F2 ≤ max (max F1 F2) F4 :=
      Nat.le_trans hle2 (Nat.le_max_left _ F4)
    have hle4' : F4 ≤ max (max F1 F2) F4 := Nat.le_max_right _ F4
    exact
      { state := hst4
        ext := (hstep1.ext.trans hx2).trans hx4
        pins := by rw [hp4, hp2, hstep1.pins]
        coh := hcoh2
        pushed := hpush2
        run := ⟨env2, max (max F1 F2) F4,
          denoteFEnv_mono hx4 hden2,
          checkDecl_opaque_pin_pure (checkConstantVal_mono hle1' hpure1)
            (checkOpaqueVal_mono hle2' hpure2) (hcont ▸ hyes)
            (checkReducePin_mono hle4' hpure4)⟩ }
  · -- the gate is skipped
    replace hgood := AM.pure_bind_ok hgood
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hgood
    have hnoP : ConLeche.reduceOpNames.contains cA.name = false := by
      rw [← hcont]
      cases hb : ns.contains cvA.name with
      | false => rfl
      | true => rw [hb] at hno; exact absurd rfl hno
    exact
      { state := hst2
        ext := hstep1.ext.trans hx2
        pins := by rw [hp2, hstep1.pins]
        coh := hcoh2
        pushed := hpush2
        run := ⟨env2, max F1 F2, hden2,
          checkDecl_opaque_pure (checkConstantVal_mono hle1 hpure1)
            (checkOpaqueVal_mono hle2 hpure2) hnoP⟩ }

/-- con-leche: ConLeche/Kernel/Checker.lean:502-560 checkDecl (the
`.axiomDecl` arm) — the widest arm of the seven: `Quot.sound`'s own record,
the standard axioms, `Lean.trustCompiler`, the two `ofReduce*` axioms, the two
positively-declined standard shapes and `sorryAx`.

**PROVED** (task #97-P3-Checker-2): six exits, assembled — `pinAt_run` and
`beq_handle_iff` for each pinned-name test, `BasisKind.decls_run` +
`IConstantInfo.canonEq_run` for the `Quot.sound` comparison,
`checkConstantVal_bridge` for the front door, the three shape tests for the
three installing families, and `IFEnvCoh.push` / `Pushed.push` /
`denoteFEnv_push` for what an install does to the environment. -/
theorem checkDecl_bridge_axiom {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {c : ConstantVal}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : Arena.checkDecl μ pins fe (.axiomDecl cv) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.axiomDecl c) s fe fe' s' := by
  simp only [Arena.checkDecl] at hrun
  obtain ⟨hnm, hlps, hty⟩ := denoteCV_inv hcv
  -- the `Quot.sound` record's own comparison, first
  obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨e1, d1⟩ :=
    pinAt_run (x := ConLeche.quotSoundName) hok.check.pins rfl g1
  rw [e1] at r1
  have hqs : (cv.name == qs) = true ↔ c.name = ConLeche.quotSoundName :=
    beq_handle_iff hok.check.state.wf hnm d1
  rcases AM.ite_ok r1 with ⟨hyes, hgood⟩ | ⟨hno, hgood⟩
  · -- the pinned quotient-soundness record: compared, installing nothing
    obtain ⟨blk, s2, g2, r2⟩ := AM.bind_ok hgood
    obtain ⟨hst2, hx2, hc2, hp2, hblk⟩ :=
      BasisKind.decls_run hok.check.state g2
    have hcv2 : Frontend.denoteCV s2.store cv = some c := denoteCV_ext hcv hx2
    cases hb4 : blk[4]? with
    | none => rw [hb4] at r2; exact absurd r2 (AM.Never.fail _ _ _ _)
    | some pinned =>
      rw [hb4] at r2
      obtain ⟨x4, hx4, hd4⟩ :=
        denoteCIList_get blk (ConLeche.BasisKind.decls .quotK) 4 pinned hblk hb4
      obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok r2
      obtain ⟨hst3, hx3, hc3, hp3, he3⟩ :=
        IConstantInfo.canonEq_run (ci := .axiomInfo cv)
          (c := ConstantInfo.axiomInfo c) hst2
          (by simp only [Frontend.denoteCI, hcv2, Option.map_some]) hd4 g3
      rcases AM.ite_ok r3 with ⟨hy3, hg3⟩ | ⟨_, hbad3⟩
      · have hext : Ext s.store s3.store := hx2.trans hx3
        have hpins3 : s3.pins = s.pins := by rw [hp3, hp2]
        have hden3 : denoteFEnv s3.store fe = some env :=
          denoteFEnv_mono hext hok.denote
        have hcanon : ConLeche.ConstantInfo.canonEq (.axiomInfo c)
            (ConLeche.quotBasis.getD 4 (.axiomInfo default)) = true := by
          show ConLeche.ConstantInfo.canonEq (.axiomInfo c)
            ((ConLeche.BasisKind.decls .quotK).getD 4
              (.axiomInfo default)) = true
          simp only [List.getD, hx4, Option.getD_some]
          exact he3 ▸ hy3
        have hpureQ : ConLeche.checkDecl μ (ConLeche.fueledOps μ 0) pinsP env
            (.axiomDecl c) = .ok env :=
          checkDecl_axiom_quotSound_pure (hqs.mp hyes) hcanon
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hg3
        exact
          { state := hst3
            ext := hext
            pins := hpins3
            coh := hok.coh
            pushed := Pushed.refl _
            run := ⟨env, 0, hden3, hpureQ⟩ }
      · exact absurd hbad3 (AM.Never.fail _ _ _ _)
  · -- the ordinary axiom route
    have hnmP : ¬ (c.name = ConLeche.quotSoundName) := fun h => hno (hqs.mpr h)
    obtain ⟨cvA, s2, g2, r2⟩ := AM.bind_ok hgood
    obtain ⟨hstep2, cA, F2, hcA, hpure2⟩ :=
      checkConstantVal_bridge hμ hk hok hcv g2
    have hok2 : FoldOK μ env fe s2 := hok.ofCore hstep2
    -- the standard-axiom shape test
    obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok r2
    obtain ⟨hst3, hx3, hc3, hp3, he3⟩ := stdAxiomOk_run hok2 hcA g3
    have hok3 : FoldOK μ env fe s3 :=
      hok2.step (hok2.check.mono hst3 hx3 hc3 hp3) hx3 hp3
    have hcA3 : Frontend.denoteCV s3.store cvA = some cA := denoteCV_ext hcA hx3
    have hnmA3 : denoteN s3.store.ns cvA.name = some cA.name :=
      (denoteCV_inv hcA3).1
    have hciA3 : Frontend.denoteCI s3.store (.axiomInfo cvA)
        = some (.axiomInfo cA) := by
      simp only [Frontend.denoteCI, hcA3, Option.map_some]
    have hext02 : Ext s.store s3.store := hstep2.ext.trans hx3
    have hpin02 : s3.pins = s.pins := by rw [hp3, hstep2.pins]
    rcases AM.ite_ok r3 with ⟨hy3, hg3⟩ | ⟨hn3, hg3⟩
    · -- a standard axiom, installed
      have hden : denoteFEnv s3.store (fe.push (.axiomInfo cvA))
          = some ⟨.axiomInfo cA :: env.consts⟩ :=
        denoteFEnv_push (denoteFEnv_mono hext02 hok.denote) hciA3
      have hpureS := checkDecl_axiom_std_pure (pinsP := pinsP) hnmP hpure2
        (he3 ▸ hy3)
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hg3
      exact
        { state := hst3
          ext := hext02
          pins := hpin02
          coh := hok.coh.push _
          pushed := Pushed.push _ _
          run := ⟨⟨.axiomInfo cA :: env.consts⟩, F2, hden, hpureS⟩ }
    · -- not a standard axiom: the three named families, then `sorryAx`
      have hstdP : ConLeche.stdAxiomOk env cA = false := by
        rw [← he3]
        cases hbb : b3 with
        | false => rfl
        | true => rw [hbb] at hn3; exact absurd rfl hn3
      obtain ⟨tc, s4, g4, r4⟩ := AM.bind_ok hg3
      obtain ⟨e4, d4⟩ :=
        pinAt_run (x := ConLeche.trustCompilerName) hok3.check.pins rfl g4
      rw [e4] at r4
      have htc : (cvA.name == tc) = true ↔ cA.name = ConLeche.trustCompilerName :=
        beq_handle_iff hst3.wf hnmA3 d4
      rcases AM.ite_ok r4 with ⟨hy4, hg4⟩ | ⟨hn4, hg4⟩
      · -- `Lean.trustCompiler`
        obtain ⟨b5, s5, g5, r5⟩ := AM.bind_ok hg4
        obtain ⟨hst5, hx5, hc5, hp5, he5⟩ := trustCompilerOk_run hok3 hcA3 g5
        rcases AM.ite_ok r5 with ⟨hy5, hg5⟩ | ⟨_, hbad5⟩
        · have hext : Ext s.store s5.store := hext02.trans hx5
          have hpins5 : s5.pins = s.pins := by rw [hp5, hpin02]
          have hden : denoteFEnv s5.store (fe.push (.axiomInfo cvA))
              = some ⟨.axiomInfo cA :: env.consts⟩ :=
            denoteFEnv_push (denoteFEnv_mono hext hok.denote)
              (denoteCI_ext hciA3 hx5)
          have hpureT := checkDecl_axiom_trust_pure (pinsP := pinsP) hnmP
            hpure2 hstdP (htc.mp hy4) (he5 ▸ hy5)
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hg5
          exact
            { state := hst5
              ext := hext
              pins := hpins5
              coh := hok.coh.push _
              pushed := Pushed.push _ _
              run := ⟨⟨.axiomInfo cA :: env.consts⟩, F2, hden, hpureT⟩ }
        · exact absurd hbad5 AM.readFail_ne
      · -- not `trustCompiler`
        have htcP : ¬ (cA.name = ConLeche.trustCompilerName) :=
          fun h => hn4 (htc.mpr h)
        obtain ⟨rn, s6, g6, r6⟩ := AM.bind_ok hg4
        obtain ⟨e6, d6⟩ :=
          pinAt_run (x := ConLeche.ofReduceNatName) hok3.check.pins rfl g6
        rw [e6] at r6
        obtain ⟨bn, s7, g7, r7⟩ := AM.bind_ok r6
        obtain ⟨e7, d7⟩ :=
          pinAt_run (x := ConLeche.ofReduceBoolName) hok3.check.pins rfl g7
        rw [e7] at r7
        have hrn : (cvA.name == rn) = true ↔ cA.name = ConLeche.ofReduceNatName :=
          beq_handle_iff hst3.wf hnmA3 d6
        have hbn : (cvA.name == bn) = true ↔ cA.name = ConLeche.ofReduceBoolName :=
          beq_handle_iff hst3.wf hnmA3 d7
        rcases AM.ite_ok r7 with ⟨hy7, hg7⟩ | ⟨hn7, hg7⟩
        · -- an `ofReduce*` axiom
          have hor : cA.name = ConLeche.ofReduceNatName ∨
              cA.name = ConLeche.ofReduceBoolName := by
            rcases Bool.or_eq_true _ _ |>.mp hy7 with h | h
            · exact Or.inl (hrn.mp h)
            · exact Or.inr (hbn.mp h)
          obtain ⟨b8, s8, g8, r8⟩ := AM.bind_ok hg7
          obtain ⟨hst8, hx8, hc8, hp8, he8⟩ := ofReduceAxOk_run hok3 hcA3 g8
          rcases AM.ite_ok r8 with ⟨hy8, hg8⟩ | ⟨_, hbad8⟩
          · have hext : Ext s.store s8.store := hext02.trans hx8
            have hpins8 : s8.pins = s.pins := by rw [hp8, hpin02]
            have hden : denoteFEnv s8.store (fe.push (.axiomInfo cvA))
                = some ⟨.axiomInfo cA :: env.consts⟩ :=
              denoteFEnv_push (denoteFEnv_mono hext hok.denote)
                (denoteCI_ext hciA3 hx8)
            have hpureR := checkDecl_axiom_ofReduce_pure (pinsP := pinsP) hnmP
              hpure2 hstdP htcP hor (he8 ▸ hy8)
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hg8
            exact
              { state := hst8
                ext := hext
                pins := hpins8
                coh := hok.coh.push _
                pushed := Pushed.push _ _
                run := ⟨⟨.axiomInfo cA :: env.consts⟩, F2, hden, hpureR⟩ }
          · exact absurd hbad8 AM.readFail_ne
        · -- neither: `propext`/`choice` decline, `sorryAx` skip, else decline
          have horP : ¬ (cA.name = ConLeche.ofReduceNatName ∨
              cA.name = ConLeche.ofReduceBoolName) := by
            intro h
            refine hn7 ?_
            rcases h with h | h
            · exact Bool.or_eq_true _ _ |>.mpr (Or.inl (hrn.mpr h))
            · exact Bool.or_eq_true _ _ |>.mpr (Or.inr (hbn.mpr h))
          obtain ⟨pe, s9, g9, r9⟩ := AM.bind_ok hg7
          obtain ⟨e9, d9⟩ :=
            pinAt_run (x := ConLeche.propextName) hok3.check.pins rfl g9
          rw [e9] at r9
          obtain ⟨ch, s10, g10, r10⟩ := AM.bind_ok r9
          obtain ⟨e10, d10⟩ :=
            pinAt_run (x := ConLeche.choiceName) hok3.check.pins rfl g10
          rw [e10] at r10
          have hpe : (cvA.name == pe) = true ↔ cA.name = ConLeche.propextName :=
            beq_handle_iff hst3.wf hnmA3 d9
          have hch : (cvA.name == ch) = true ↔ cA.name = ConLeche.choiceName :=
            beq_handle_iff hst3.wf hnmA3 d10
          rcases AM.ite_ok r10 with ⟨_, hbad10⟩ | ⟨hn10, hg10⟩
          · exact absurd hbad10 AM.readFail_ne
          · have hstdShape : ¬ (cA.name = ConLeche.propextName ∨
                cA.name = ConLeche.choiceName) := by
              intro h
              refine hn10 ?_
              rcases h with h | h
              · exact Bool.or_eq_true _ _ |>.mpr (Or.inl (hpe.mpr h))
              · exact Bool.or_eq_true _ _ |>.mpr (Or.inr (hch.mpr h))
            obtain ⟨sa, s11, g11, r11⟩ := AM.bind_ok hg10
            obtain ⟨e11, d11⟩ :=
              pinAt_run (x := ConLeche.sorryAxName) hok3.check.pins rfl g11
            rw [e11] at r11
            have hsa : (cvA.name == sa) = true ↔ cA.name = ConLeche.sorryAxName :=
              beq_handle_iff hst3.wf hnmA3 d11
            rcases AM.ite_ok r11 with ⟨hy11, hg11⟩ | ⟨_, hbad11⟩
            · have hden : denoteFEnv s3.store fe = some env :=
                denoteFEnv_mono hext02 hok.denote
              have hpureA := checkDecl_axiom_sorryAx_pure (pinsP := pinsP) hnmP
                hpure2 hstdP htcP horP hstdShape (hsa.mp hy11)
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hg11
              exact
                { state := hst3
                  ext := hext02
                  pins := hpin02
                  coh := hok.coh
                  pushed := Pushed.refl _
                  run := ⟨env, F2, hden, hpureA⟩ }
            · exact absurd hbad11 AM.readFail_ne

/-- con-leche: ConLeche/Kernel/Checker.lean:562 checkDecl (the `.basisDecl`
arm) — the fold's own pinned-block record.

**PROVED** (task #97-P3-Checker-2): the arm IS `checkBasisDecl`, on both
sides. -/
theorem checkDecl_bridge_basis {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {kind : BasisKind}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hrun : Arena.checkDecl μ pins fe (.basisDecl kind) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.basisDecl kind) s fe fe' s' := by
  simp only [Arena.checkDecl] at hrun
  obtain ⟨hst, hx, hp, hcoh, hpush, env', hden, hpure⟩ :=
    checkBasisDecl_bridge (μ := μ) (F := 0) hok hrun
  exact
    { state := hst, ext := hx, pins := hp, coh := hcoh, pushed := hpush
      run := ⟨env', 0, hden, checkDecl_basis_pure hpure⟩ }

/-- con-leche: ConLeche/Kernel/Checker.lean:564-600 checkDecl (the `.indDecl`
arm) — **the one arm this tier does not own**.  The recogniser
(`basisPinHit`) is `Bridge/Checker/Basis.lean`'s and the route behind it is
`IndSpec`, the named hypothesis.

**PROVED** (task #97-P3-Checker-2): `basisPinHit_run` for the recogniser,
then `checkBasisDecl_bridge` on the pinned route and `IndSpec.run` verbatim on
the other — the only one of the seven whose remaining content is a
*hypothesis* rather than a proof. -/
theorem checkDecl_bridge_ind {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {nP : Nat}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : Arena.checkDecl μ pins fe (.indDecl block nP) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.indDecl b nP) s fe fe' s' := by
  simp only [Arena.checkDecl] at hrun
  obtain ⟨r, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, hx1, hc1, hp1, hr1⟩ := basisPinHit_run hok.check.state hb g1
  have hok1 : FoldOK μ env fe s1 :=
    hok.step (hok.check.mono hst1 hx1 hc1 hp1) hx1 hp1
  have hb1 : Frontend.denoteCIList s1.store block = some b :=
    denoteCIList_mono hx1 _ _ hb
  cases r with
  | some kind =>
    obtain ⟨hst, hx, hp, hcoh, hpush, env', hden, hpure⟩ :=
      checkBasisDecl_bridge (μ := μ) (F := 0) hok1 r1
    exact
      { state := hst
        ext := hx1.trans hx
        pins := by rw [hp, hp1]
        coh := hcoh
        pushed := hpush
        run := ⟨env', 0, hden, checkDecl_ind_basis_pure hr1.symm hpure⟩ }
  | none =>
    obtain ⟨hst, hx, hp, hcoh, hpush, hvis, env', F, hden, hpure⟩ :=
      hind.run (pinsP := pinsP) hok1 hb1 hr1.symm r1
    exact
      { state := hst
        ext := hx1.trans hx
        pins := by rw [hp, hp1]
        coh := hcoh
        pushed := hpush
        run := ⟨env', F, hden, hpure⟩ }

/-- con-leche: ConLeche/Kernel/Checker.lean:602-626 checkDecl (the `.quotDecl`
arm) — the four-record quotient package, the first matching record installing
the pinned block whole.

**PROVED** (task #97-P3-Checker-2): `quotPinHit_run` for the recogniser and
`checkBasisDecl_bridge` for the `.type` record's install; the other four
kinds install nothing, so their `Pushed` is `refl` and their environment is
the one they arrived at. -/
theorem checkDecl_bridge_quot {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {k : QuotKind} {cv : IConstantVal}
    {c : ConstantVal}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : Arena.checkDecl μ pins fe (.quotDecl k cv) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.quotDecl k c) s fe fe' s' := by
  simp only [Arena.checkDecl] at hrun
  obtain ⟨b, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, hx1, hc1, hp1, hb1⟩ := quotPinHit_run hok.check.state hcv g1
  have hok1 : FoldOK μ env fe s1 :=
    hok.step (hok.check.mono hst1 hx1 hc1 hp1) hx1 hp1
  rcases AM.ite_ok r1 with ⟨hb, hgood⟩ | ⟨_, hbad⟩
  · have hhit : ConLeche.quotPinHit k c = true := by rw [← hb1]; exact hb
    cases k with
    | type =>
      obtain ⟨hst, hx, hp, hcoh, hpush, env', hden, hpure⟩ :=
        checkBasisDecl_bridge (μ := μ) (F := 0) hok1 hgood
      exact
        { state := hst
          ext := hx1.trans hx
          pins := by rw [hp, hp1]
          coh := hcoh
          pushed := hpush
          run := ⟨env', 0, hden, checkDecl_quot_type_pure hhit hpure⟩ }
    | ctor | lift | ind | sound =>
      all_goals (
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hgood
        exact
          { state := hst1
            ext := hx1
            pins := hp1
            coh := hok.coh
            pushed := Pushed.refl _
            run := ⟨env, 0, hok1.denote,
              checkDecl_quot_other_pure (by simp) hhit⟩ })
  · exact absurd hbad (AM.Never.fail _ _ _ _)

end ConRon.Bridge
