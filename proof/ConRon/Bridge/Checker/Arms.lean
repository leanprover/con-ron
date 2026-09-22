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

/-! ## The seven arms -/

/-- con-leche: ConLeche/Kernel/Checker.lean:441-484 checkDecl (the `.defnDecl`
arm) — a definition, with the two `Nat`-operation pin gates behind it.

`sorry`: `checkConstantVal_bridge` and `checkDefnVal_bridge`
(`Bridge/Checker/Base.lean`), then `natOpGuard` / `certifyNatEqs` /
`checkDivModPin` (`Arena/DeclCheck.lean`), each of which is a `KnotSpec`
consumer over a pinned term.  Task #97-P3-Checker's sorry list, item 7. -/
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

`sorry`: `IConstantInfo.canonEq`'s exactness (`Bridge/Checker/Canon.lean`),
`stdAxiomOk` / `trustCompilerOk` / `ofReduceAxOk` (`Arena/DeclCheck.lean`) and
the pin readers' denotations.  Task #97-P3-Checker's sorry list, item 7. -/
theorem checkDecl_bridge_axiom {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {c : ConstantVal}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : Arena.checkDecl μ pins fe (.axiomDecl cv) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.axiomDecl c) s fe fe' s' := by
  sorry

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
