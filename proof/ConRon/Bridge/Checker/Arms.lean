/-
# `ConRon.Bridge.Checker.Arms` — `checkDeclKind`'s six arms

`Bridge/Checker/Decl.lean` states what an arm concludes (`DeclKindOut`) and what relates the two
pin lists (`PinsDenote`); this module is the six arms themselves.  Every one is an ASSEMBLY, a chain
of `AM.bind_ok` inversions over statements that live one tier down, closed by a pure step lemma
about con-leche's own `checkDeclKind` clause (`ConLeche/Kernel/CheckDecl.lean`).

| arm | what it needs |
|---|---|
| `defn` | `checkConstantVal_bridge`, `checkDefnVal_bridge`, the structural-`Nat` and `Nat.div`/`Nat.mod` gates (`Bridge/Checker/DeclVal.lean`, `DivMod.lean`) |
| `thm` / `opaque` | the front door, the value check; `opaque` also the `reduce*` gate |
| `axiom` | the pinned-name tests, `checkQuotRecord_bridge` at `Quot.sound`, the shape tests (`Bridge/Checker/Basis.lean`) |
| `ind` | `IndSpec` (the uniform route at every block, the pinned basis blocks included) |
| `quot` | `checkDeclKind_bridge_quot` (`Bridge/Checker/Basis.lean`) |

A value arm checks the value, getting the record back unpushed; the gates run at the index with
the record pushed and popped again (`IFEnv.SameView`); the arm pushes last.  What the record pushes
is not this module's concern: `DeclKindOut` concludes con-leche's step only.
-/
module

import ConRon.Bridge.Checker.DivMod
public import ConRon.Bridge.Checker.DeclVal
import ConLeche.Verify.Extend.Inversions
public import ConRon.Bridge.Checker.Decl
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.NatOpNames
public import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.EnvDenote

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## Carrying the invariant across a step -/

/-- con-leche: none — `FoldOK` across a `CoreStep`, which is what every core consumer hands
back. -/
theorem FoldOK.ofCore {env : Env} {fe : IFEnv} {s s' : AState}
    (h : FoldOK env fe s) (hc : CoreStep env fe s s') :
    FoldOK env fe s' := h.step hc.ok hc.pins

/-- con-leche: none — `FoldOK` at an index with the same view: the own index row for row, the
lookups, the table map, the frozen layer and the list. -/
theorem FoldOK.sameView {env : Env} {fe fe' : IFEnv} {s : AState}
    (h : FoldOK env fe s) (hsv : ConRon.Bridge.IFEnv.SameView fe' fe) : FoldOK env fe' s where
  check := h.check.congr_find hsv.find hsv.tbls hsv.base
  envWF := h.envWF
  tblShape := by rw [hsv.env]; exact h.tblShape
  persPins := h.persPins
  coh := ⟨fun n => by rw [hsv.idx n, hsv.env]; exact h.coh.idx n,
    fun n => by rw [hsv.tbls, hsv.env]; exact h.coh.tbls n⟩
  gate := fun n t ht => by
    have hr : fe'.rawTable? n = fe.rawTable? n := by simp only [IFEnv.rawTable?, hsv.tbls, hsv.base]
    rw [hsv.find n]; exact h.gate n t (hr ▸ ht)

/-! ## The pure side's step lemmas

One lemma per clause of con-leche's `checkDeclKind`, in the shape the arm's last step produces. -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the `.thmDecl`
arm). -/
theorem checkDecl_thm_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env' : Env} {c : ConstantVal} {x : Expr}
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ())
    (h2 : ConLeche.checkThmVal (ConLeche.fueledOps μ F) env c x = .ok env') :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.thmDecl c x)
      = .ok env' := by
  simp only [ConLeche.checkDeclKind, h1, h2, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the
`.opaqueDecl` arm) with the compiler-trust gate NOT taken. -/
theorem checkDecl_opaque_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env2 : Env} {c : ConstantVal} {x : Expr}
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ())
    (h2 : ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env2)
    (h3 : ConLeche.reduceOpNames.contains c.name = false) :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.opaqueDecl c x)
      = .ok env2 := by
  simp only [ConLeche.checkDeclKind, h1, h2, h3, Bool.false_eq_true, ite_false, bind,
    Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the
`.opaqueDecl` arm) with the compiler-trust gate TAKEN. -/
theorem checkDecl_opaque_pin_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env2 : Env} {c : ConstantVal} {x : Expr}
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ())
    (h2 : ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env2)
    (h3 : ConLeche.reduceOpNames.contains c.name = true)
    (h4 : ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 c.name x
      = .ok ()) :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.opaqueDecl c x)
      = .ok env2 := by
  simp only [ConLeche.checkDeclKind, h1, h2, h3, h4, ite_true, bind, Except.bind,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the `.defnDecl` arm) — the two
gates, each taken exactly when its name list contains the definition's name. -/
theorem checkDecl_defn_pure {F : Nat} {pinsP : List NatOpPinSet} {env env2 : Env}
    {c : ConstantVal} {x : Expr} {hint : ReducibilityHint}
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps .verified F) env c true = .ok ())
    (h2 : ConLeche.checkDefnVal (ConLeche.fueledOps .verified F) env c x hint = .ok env2)
    (h3 : ConLeche.natOpNames.contains c.name = true →
      (ConLeche.natOpGuard env2 c.name &&
        (ConLeche.natOpDeps c.name).all (ConLeche.natOpStoredOk env2)) = true ∧
      ∃ cv' v' hint', env2.find? c.name = some (.defnInfo cv' v' hint') ∧
        ConLeche.certifyNatEqs (ConLeche.fueledOps .verified F) env
          ((ConLeche.natOpEquations 0 c.name).map fun eq =>
            (Expr.substConst0 c.name v' eq.1, Expr.substConst0 c.name v' eq.2)) = .ok true)
    (h4 : ConLeche.natDivModNames.contains c.name = true →
      ConLeche.checkDivModPin (ConLeche.fueledOps .verified F) pinsP env env2 c.name = .ok ()) :
    ConLeche.checkDeclKind (ConLeche.fueledOps .verified F) pinsP env (.defnDecl c x hint)
      = .ok env2 := by
  cases hn : ConLeche.natOpNames.contains c.name <;>
    cases hd : ConLeche.natDivModNames.contains c.name
  · simp only [ConLeche.checkDeclKind, h1, h2, hn, hd, bind, Except.bind, Bool.false_eq_true,
      ite_false, pure, Except.pure]
  · simp only [ConLeche.checkDeclKind, h1, h2, hn, hd, h4 hd, bind, Except.bind, Bool.false_eq_true,
      ite_false, ite_true, pure, Except.pure]
  · obtain ⟨hg, cv', v', hint', hf, hc⟩ := h3 hn
    simp only [ConLeche.checkDeclKind, h1, h2, hn, hd, hg, hf, hc, bind, Except.bind,
      Bool.false_eq_true, ite_false, ite_true, pure, Except.pure]
  · obtain ⟨hg, cv', v', hint', hf, hc⟩ := h3 hn
    simp only [ConLeche.checkDeclKind, h1, h2, hn, hd, hg, hf, hc, h4 hd, bind, Except.bind,
      ite_true, pure, Except.pure]

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

/-! ### The `.axiomDecl` arm's six exits -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind — the
`Quot.sound` record: the quotient package's own record, compared with its pin and
installed at its names. -/
theorem checkDecl_axiom_quotSound_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env env' : Env} {c : ConstantVal}
    (hnm : c.name = ConLeche.quotSoundName)
    (h : ConLeche.checkQuotRecord (m := CheckM) env .sound c = .ok env') :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok env' := by
  simp only [ConLeche.checkDeclKind, hnm, ite_true]; exact h

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind — a standard
axiom, installed. -/
theorem checkDecl_axiom_std_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ())
    (h2 : ConLeche.stdAxiomOk env c = true) :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok ⟨.axiomInfo c :: env.consts, env.tables⟩ := by
  simp only [ConLeche.checkDeclKind, ite_eq_right hnm, h1, h2, ite_true, bind, Except.bind,
    pure, Except.pure]

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind —
`Lean.trustCompiler`, installed. -/
theorem checkDecl_axiom_trust_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ())
    (h2 : ConLeche.stdAxiomOk env c = false)
    (h3 : c.name = ConLeche.trustCompilerName)
    (h4 : ConLeche.trustCompilerOk env c = true) :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok ⟨.axiomInfo c :: env.consts, env.tables⟩ := by
  have hnm' : ¬ (ConLeche.trustCompilerName = ConLeche.quotSoundName) := h3 ▸ hnm
  simp only [ConLeche.checkDeclKind, h1, h2, h3, h4, ite_eq_right hnm', Bool.false_eq_true,
    ite_false, ite_true, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind — an
`ofReduce*` axiom, installed. -/
theorem checkDecl_axiom_ofReduce_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ())
    (h2 : ConLeche.stdAxiomOk env c = false)
    (h3 : ¬ (c.name = ConLeche.trustCompilerName))
    (h4 : c.name = ConLeche.ofReduceNatName ∨
      c.name = ConLeche.ofReduceBoolName)
    (h5 : ConLeche.ofReduceAxOk env c = true) :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok ⟨.axiomInfo c :: env.consts, env.tables⟩ := by
  simp only [ConLeche.checkDeclKind, ite_eq_right hnm, h1, h2, h5, Bool.false_eq_true,
    ite_false, ite_true, ite_eq_right h3, ite_eq_left h4, bind, Except.bind, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind — `sorryAx`, the
one axiom the checker tolerates as a DECLARATION: skipped, installing
nothing. -/
theorem checkDecl_axiom_sorryAx_pure {μ : CheckMode} {F : Nat}
    {pinsP : List NatOpPinSet} {env : Env} {c : ConstantVal}
    (hnm : ¬ (c.name = ConLeche.quotSoundName))
    (h1 : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok ())
    (h2 : ConLeche.stdAxiomOk env c = false)
    (h3 : ¬ (c.name = ConLeche.trustCompilerName))
    (h4 : ¬ (c.name = ConLeche.ofReduceNatName ∨
      c.name = ConLeche.ofReduceBoolName))
    (h5 : ¬ (c.name = ConLeche.propextName ∨ c.name = ConLeche.choiceName))
    (h6 : c.name = ConLeche.sorryAxName) :
    ConLeche.checkDeclKind (ConLeche.fueledOps μ F) pinsP env (.axiomDecl c)
      = .ok env := by
  simp only [ConLeche.checkDeclKind, ite_eq_right hnm, h1, h2, Bool.false_eq_true,
    ite_false, ite_eq_right h3, ite_eq_right h4, ite_eq_right h5, ite_eq_left h6, bind, Except.bind,
    pure, Except.pure]

/-! ## The arms -/

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the `.thmDecl` arm): the front
door and the value check, at one fuel. -/
theorem checkDeclKind_bridge_thm
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {c : ConstantVal} {x : Expr}
    (hk : CoreSpec Arena.checkFuel)
    (hok : FoldOK env fe s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : Arena.checkDeclKind .verified pins fe (.thmDecl cv value) s = .ok (fe', s')) :
    DeclKindOut pinsP env (.thmDecl c x) s s' := by
  simp only [Arena.checkDeclKind] at hrun
  obtain ⟨_, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, F1, hpure1⟩ := checkConstantVal_bridge_of_fold hk hok hcv g1
  have hcA : Frontend.denoteCV s1.store cv = some c := denoteCV_ext hcv hstep1.ext
  have hok1 : FoldOK env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  obtain ⟨ci, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hstep2, -, -, -, -, F2, hpure2⟩ :=
    checkThmVal_bridge hk hok1 hcA (checkConstantVal_typeWF hpure1) hv1 g2
  obtain ⟨-, rfl⟩ := AM.pure_ok r2
  exact ⟨hstep2.ok.state, hstep1.ext.trans hstep2.ext, by rw [hstep2.pins, hstep1.pins], _,
    max F1 F2, checkDecl_thm_pure (checkConstantVal_mono (Nat.le_max_left _ _) hpure1)
      (checkThmVal_mono (Nat.le_max_right _ _) hpure2)⟩

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the `.opaqueDecl` arm), with the
compiler-trust `reduce*` gate behind it. -/
theorem checkDeclKind_bridge_opaque
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {c : ConstantVal} {x : Expr}
    (hk : CoreSpec Arena.checkFuel)
    (hok : FoldOK env fe s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : Arena.checkDeclKind .verified pins fe (.opaqueDecl cv value) s = .ok (fe', s')) :
    DeclKindOut pinsP env (.opaqueDecl c x) s s' := by
  simp only [Arena.checkDeclKind] at hrun
  obtain ⟨_, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, F1, hpure1⟩ := checkConstantVal_bridge_of_fold hk hok hcv g1
  have hcA : Frontend.denoteCV s1.store cv = some c := denoteCV_ext hcv hstep1.ext
  have hok1 : FoldOK env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  obtain ⟨ci, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hstep2, rfl, hci2, hcw2, hsh2, F2, hpure2⟩ :=
    checkOpaqueVal_bridge hk hok1 hcA (checkConstantVal_typeWF hpure1) hv1 g2
  have hx2 : Ext s1.store s2.store := hstep2.ext
  have hok2 : FoldOK env fe s2 := hok1.ofCore hstep2
  have hnm2 : denoteN s2.store.ns cv.name = some c.name :=
    denoteN_ext (denoteCV_inv hcA).1 hx2
  have hv2 : denoteE s2.store value = some x := denote_ext hv1 hx2
  have hle1 : F1 ≤ max F1 F2 := Nat.le_max_left _ _
  have hle2 : F2 ≤ max F1 F2 := Nat.le_max_right _ _
  -- the compiler-trust gate
  obtain ⟨ns, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨rfl, hns⟩ := reduceOpNames_run hok2.check.pins g3
  have hcont : ns.contains cv.name = ConLeche.reduceOpNames.contains c.name :=
    denoteNList_contains hok2.check.state.wf ns ConLeche.reduceOpNames
      (denoteNL_toList ns ConLeche.reduceOpNames hns) cv.name c.name hnm2
  rcases AM.ite_ok r3 with ⟨hyes, hgood⟩ | ⟨hno, hgood⟩
  · obtain ⟨fe4, s4, g4, r4⟩ := AM.bind_ok hgood
    have hok2' : StepOK ⟨.axiomInfo c :: env.consts, env.tables⟩ (fe.push (.axiomInfo cv)) s3 :=
      hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2
    obtain ⟨hstep4, -, F4, hpure4⟩ :=
      checkReducePin_bridge hk hok2.check hok2.envWF hok2' rfl hnm2 hv2
        (ConLeche.Expr.WScoped.of_not_hasFvar (checkOpaqueVal_noFvar hpure2)) g4
    obtain ⟨-, rfl⟩ := AM.pure_ok r4
    exact ⟨hstep4.ok.state, (hstep1.ext.trans hx2).trans hstep4.ext,
      by rw [hstep4.pins, hstep2.pins, hstep1.pins], _, max (max F1 F2) F4,
      checkDecl_opaque_pin_pure
        (checkConstantVal_mono (Nat.le_trans hle1 (Nat.le_max_left _ F4)) hpure1)
        (checkOpaqueVal_mono (Nat.le_trans hle2 (Nat.le_max_left _ F4)) hpure2) (hcont ▸ hyes)
        (checkReducePin_mono (Nat.le_max_right _ F4) hpure4)⟩
  · replace hgood := AM.pure_bind_ok hgood
    obtain ⟨-, rfl⟩ := AM.pure_ok hgood
    have hnoP : ConLeche.reduceOpNames.contains c.name = false := by
      rw [← hcont]
      cases hb : ns.contains cv.name with
      | false => rfl
      | true => rw [hb] at hno; exact absurd rfl hno
    exact ⟨hstep2.ok.state, hstep1.ext.trans hx2, by rw [hstep2.pins, hstep1.pins], _, max F1 F2,
      checkDecl_opaque_pure (checkConstantVal_mono hle1 hpure1)
        (checkOpaqueVal_mono hle2 hpure2) hnoP⟩

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the `.defnDecl` arm): the front
door with a certified operation's name allowed, the value check, the structural-`Nat` gate and the
`Nat.div`/`Nat.mod` gate, each at the index with the record pushed and popped. -/
theorem checkDeclKind_bridge_defn
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {hint : ReducibilityHint} {c : ConstantVal} {x : Expr}
    (hk : CoreSpec Arena.checkFuel)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : Arena.checkDeclKind .verified pins fe (.defnDecl cv value hint) s = .ok (fe', s')) :
    DeclKindOut pinsP env (.defnDecl c x hint) s s' := by
  simp only [Arena.checkDeclKind] at hrun
  obtain ⟨_, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, F1, hpure1⟩ := checkConstantVal_bridge_of_fold hk hok hcv g1
  have hcA : Frontend.denoteCV s1.store cv = some c := denoteCV_ext hcv hstep1.ext
  have hok1 : FoldOK env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  obtain ⟨ci, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hstep2, rfl, hci2, hcw2, hsh2, F2, hpure2⟩ :=
    checkDefnVal_bridge hk hok1 hcA (checkConstantVal_typeWF hpure1) hv1 g2
  have hok2 : FoldOK env fe s2 := hok1.ofCore hstep2
  have hnm2 : denoteN s2.store.ns cv.name = some c.name :=
    denoteN_ext (denoteCV_inv hcA).1 hstep2.ext
  -- the structural-`Nat` gate
  obtain ⟨ns, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨e3, hns⟩ := natOpNames_run hok2.check.pins g3
  rw [e3] at r3
  have hcont : ns.contains cv.name = ConLeche.natOpNames.contains c.name :=
    denoteNList_contains hok2.check.state.wf ns ConLeche.natOpNames
      (denoteNL_toList ns ConLeche.natOpNames hns) cv.name c.name hnm2
  have hle1 : F1 ≤ max F1 F2 := Nat.le_max_left _ _
  have hle2 : F2 ≤ max F1 F2 := Nat.le_max_right _ _
  -- the rest, from the index the first gate hands back
  have tail : ∀ (fe3 : IFEnv) (s4 : AState) (Fa : Nat), CoreStep env fe s2 s4 →
      ConRon.Bridge.IFEnv.SameView fe3 fe →
      (ConLeche.natOpNames.contains c.name = true →
        (ConLeche.natOpGuard ⟨.defnInfo c x hint :: env.consts, env.tables⟩ c.name &&
          (ConLeche.natOpDeps c.name).all
            (ConLeche.natOpStoredOk ⟨.defnInfo c x hint :: env.consts, env.tables⟩)) = true ∧
        ∃ cv' v' hint', (⟨.defnInfo c x hint :: env.consts, env.tables⟩ : Env).find? c.name =
            some (.defnInfo cv' v' hint') ∧
          ConLeche.certifyNatEqs (ConLeche.fueledOps .verified Fa) env
            ((ConLeche.natOpEquations 0 c.name).map fun eq =>
              (Expr.substConst0 c.name v' eq.1, Expr.substConst0 c.name v' eq.2)) = .ok true) →
      (do
          let d ← Arena.natDivModNames
          if d.contains cv.name = true then do
            let y ← Arena.checkDivModPin .verified pins fe3 (.defnInfo cv value hint) cv.name
            pure (y.push (.defnInfo cv value hint))
          else do
            let y ← pure fe3
            pure (y.push (.defnInfo cv value hint))) s4 = .ok (fe', s') →
      DeclKindOut pinsP env (.defnDecl c x hint) s s' := by
    intro fe3 s4 Fa hstep4 hsv4 hG r4
    have hok4 : FoldOK env fe3 s4 := (hok2.ofCore hstep4).sameView hsv4
    have hnm4 : denoteN s4.store.ns cv.name = some c.name := denoteN_ext hnm2 hstep4.ext
    have hci4 : Frontend.denoteCI s4.store (.defnInfo cv value hint) =
        some (.defnInfo c x hint) := denoteCI_ext hci2 hstep4.ext
    obtain ⟨ds, s5, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨e5, hds⟩ := natDivModNames_run hok4.check.pins g5
    rw [e5] at r5
    have hcontD : ds.contains cv.name = ConLeche.natDivModNames.contains c.name :=
      denoteNList_contains hok4.check.state.wf ds ConLeche.natDivModNames
        (denoteNL_toList ds ConLeche.natDivModNames hds) cv.name c.name hnm4
    have hx4 : Ext s.store s4.store := (hstep1.ext.trans hstep2.ext).trans hstep4.ext
    have hp4 : s4.pins = s.pins := by rw [hstep4.pins, hstep2.pins, hstep1.pins]
    have hGF : ∀ F, max (max F1 F2) Fa ≤ F → ConLeche.natOpNames.contains c.name = true →
        (ConLeche.natOpGuard ⟨.defnInfo c x hint :: env.consts, env.tables⟩ c.name &&
          (ConLeche.natOpDeps c.name).all
            (ConLeche.natOpStoredOk ⟨.defnInfo c x hint :: env.consts, env.tables⟩)) = true ∧
        ∃ cv' v' hint', (⟨.defnInfo c x hint :: env.consts, env.tables⟩ : Env).find? c.name =
            some (.defnInfo cv' v' hint') ∧
          ConLeche.certifyNatEqs (ConLeche.fueledOps .verified F) env
            ((ConLeche.natOpEquations 0 c.name).map fun eq =>
              (Expr.substConst0 c.name v' eq.1, Expr.substConst0 c.name v' eq.2)) = .ok true := by
      intro F hF hn
      obtain ⟨hg, cv', v', hint', hf, hc⟩ := hG hn
      exact ⟨hg, cv', v', hint', hf, certifyNatEqs_mono (by omega) hc⟩
    rcases AM.ite_ok r5 with ⟨hyes, k5⟩ | ⟨hno, k5⟩
    · obtain ⟨fe5, s6, g6, r6⟩ := AM.bind_ok k5
      obtain ⟨-, rfl⟩ := AM.pure_ok r6
      have hok4' := hok4.toStepOK.push hok4.check.state hci4 hsh2 hcw2
      obtain ⟨hstep6, -, Fb, hFb⟩ := checkDivModPin_bridge hk hok4.check hok4.envWF hok4' rfl
        (PinsDenote.mono hx4 _ _ hpins) hnm4 g6
      exact ⟨hstep6.ok.state, hx4.trans hstep6.ext, by rw [hstep6.pins, hp4], _,
        max (max (max F1 F2) Fa) Fb,
        checkDecl_defn_pure (checkConstantVal_mono (by omega) hpure1)
          (checkDefnVal_mono (by omega) hpure2) (hGF _ (by omega))
          (fun _ => checkDivModPin_mono (by omega) hFb)⟩
    · replace k5 := AM.pure_bind_ok k5
      obtain ⟨-, rfl⟩ := AM.pure_ok k5
      exact ⟨hok4.check.state, hx4, hp4, _, max (max F1 F2) Fa,
        checkDecl_defn_pure (checkConstantVal_mono (by omega) hpure1)
          (checkDefnVal_mono (by omega) hpure2) (hGF _ (Nat.le_refl _))
          (fun h => absurd (hcontD ▸ h) hno)⟩
  rcases AM.ite_ok r3 with ⟨hyes, k3⟩ | ⟨hno, k3⟩
  · obtain ⟨fe3, s4, g4, r4⟩ := AM.bind_ok k3
    have hok2' := hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2
    obtain ⟨hs, hsv, hgd, cv', v', hint', F, hf, hc⟩ :=
      checkStructuralNatPin_bridge hk hok2.check hok2.envWF hok2' rfl hnm2 g4
    exact tail fe3 s4 F hs hsv (fun _ => ⟨hgd, cv', v', hint', hf, hc⟩) r4
  · replace k3 := AM.pure_bind_ok k3
    exact tail fe s2 0 (CoreStep.refl hok2.check) ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl⟩
      (fun h => absurd (hcont ▸ h) hno) k3

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the `.indDecl` arm): the
uniform route at every block, which is `IndSpec`. -/
theorem checkDeclKind_bridge_ind
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {nP : Nat}
    (hind : IndSpec) (hok : FoldOK env fe s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : Arena.checkDeclKind .verified pins fe (.indDecl block nP) s = .ok (fe', s')) :
    DeclKindOut pinsP env (.indDecl b nP) s s' := by
  simp only [Arena.checkDeclKind] at hrun
  obtain ⟨hst, hx, hp, hrun'⟩ := hind.run (pinsP := pinsP) hok hb hrun
  exact ⟨hst, hx, hp, hrun'⟩

/-- con-leche: ConLeche/Kernel/CheckDecl.lean:27-164 checkDeclKind (the `.axiomDecl` arm):
`Quot.sound`'s own comparison, else the front door and the pinned-name tests. -/
theorem checkDeclKind_bridge_axiom
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {c : ConstantVal}
    (hk : CoreSpec Arena.checkFuel)
    (hok : FoldOK env fe s) (_hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : Arena.checkDeclKind .verified pins fe (.axiomDecl cv) s = .ok (fe', s')) :
    DeclKindOut pinsP env (.axiomDecl c) s s' := by
  simp only [Arena.checkDeclKind] at hrun
  obtain ⟨hnm, hlps, hty⟩ := denoteCV_inv hcv
  -- the `Quot.sound` record's own comparison, first
  obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨e1, d1⟩ :=
    pinAt_run (x := ConLeche.quotSoundName) hok.check.pins rfl g1
  rw [e1] at r1
  have hqs : (cv.name == qs) = true ↔ c.name = ConLeche.quotSoundName :=
    beq_handle_iff hok.check.state.wf hnm d1
  rcases AM.ite_ok r1 with ⟨hyes, hgood⟩ | ⟨hno, hgood⟩
  · -- the quotient package's own record
    obtain ⟨hst2, hx2, hp2, env', hq⟩ := checkQuotRecord_bridge hok hcv hgood
    exact ⟨hst2, hx2, hp2, env', 0, checkDecl_axiom_quotSound_pure (hqs.mp hyes) hq⟩
  · -- the ordinary axiom route
    have hnmP : ¬ (c.name = ConLeche.quotSoundName) := fun h => hno (hqs.mpr h)
    obtain ⟨_, s2, g2, r2⟩ := AM.bind_ok hgood
    obtain ⟨hstep2, F2, hpure2⟩ :=
      checkConstantVal_bridge_of_fold hk hok hcv g2
    have hcA : Frontend.denoteCV s2.store cv = some c := denoteCV_ext hcv hstep2.ext
    have hok2 : FoldOK env fe s2 := hok.ofCore hstep2
    -- the standard-axiom shape test
    obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok r2
    obtain ⟨hst3, hx3, hc3, hp3, he3⟩ := stdAxiomOk_run hok2 hcA g3
    have hok3 : FoldOK env fe s3 :=
      hok2.step (hok2.check.mono hst3 hx3 hc3 hp3) hp3
    have hcA3 : Frontend.denoteCV s3.store cv = some c := denoteCV_ext hcA hx3
    have hnmA3 : denoteN s3.store.ns cv.name = some c.name :=
      (denoteCV_inv hcA3).1
    have hciA3 : Frontend.denoteCI s3.store (.axiomInfo cv)
        = some (.axiomInfo c) := by
      simp only [Frontend.denoteCI, hcA3, Option.map_some]
    have hext02 : Ext s.store s3.store := hstep2.ext.trans hx3
    have hpin02 : s3.pins = s.pins := by rw [hp3, hstep2.pins]
    rcases AM.ite_ok r3 with ⟨hy3, hg3⟩ | ⟨hn3, hg3⟩
    · -- a standard axiom, installed
      have hpureS := checkDecl_axiom_std_pure (pinsP := pinsP) hnmP hpure2
        (he3 ▸ hy3)
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hg3
      exact ⟨hst3, hext02, hpin02, ⟨.axiomInfo c :: env.consts, env.tables⟩, F2, hpureS⟩
    · -- not a standard axiom: the three named families, then `sorryAx`
      have hstdP : ConLeche.stdAxiomOk env c = false := by
        rw [← he3]
        cases hbb : b3 with
        | false => rfl
        | true => rw [hbb] at hn3; exact absurd rfl hn3
      obtain ⟨tc, s4, g4, r4⟩ := AM.bind_ok hg3
      obtain ⟨e4, d4⟩ :=
        pinAt_run (x := ConLeche.trustCompilerName) hok3.check.pins rfl g4
      rw [e4] at r4
      have htc : (cv.name == tc) = true ↔ c.name = ConLeche.trustCompilerName :=
        beq_handle_iff hst3.wf hnmA3 d4
      rcases AM.ite_ok r4 with ⟨hy4, hg4⟩ | ⟨hn4, hg4⟩
      · -- `Lean.trustCompiler`
        obtain ⟨b5, s5, g5, r5⟩ := AM.bind_ok hg4
        obtain ⟨hst5, hx5, hc5, hp5, he5⟩ := trustCompilerOk_run hok3 hcA3 g5
        rcases AM.ite_ok r5 with ⟨hy5, hg5⟩ | ⟨_, hbad5⟩
        · have hext : Ext s.store s5.store := hext02.trans hx5
          have hpins5 : s5.pins = s.pins := by rw [hp5, hpin02]
          have hpureT := checkDecl_axiom_trust_pure (pinsP := pinsP) hnmP
            hpure2 hstdP (htc.mp hy4) (he5 ▸ hy5)
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hg5
          exact ⟨hst5, hext, hpins5, ⟨.axiomInfo c :: env.consts, env.tables⟩, F2, hpureT⟩
        · exact absurd hbad5 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
      · -- not `trustCompiler`
        have htcP : ¬ (c.name = ConLeche.trustCompilerName) :=
          fun h => hn4 (htc.mpr h)
        obtain ⟨rn, s6, g6, r6⟩ := AM.bind_ok hg4
        obtain ⟨e6, d6⟩ :=
          pinAt_run (x := ConLeche.ofReduceNatName) hok3.check.pins rfl g6
        rw [e6] at r6
        obtain ⟨bn, s7, g7, r7⟩ := AM.bind_ok r6
        obtain ⟨e7, d7⟩ :=
          pinAt_run (x := ConLeche.ofReduceBoolName) hok3.check.pins rfl g7
        rw [e7] at r7
        have hrn : (cv.name == rn) = true ↔ c.name = ConLeche.ofReduceNatName :=
          beq_handle_iff hst3.wf hnmA3 d6
        have hbn : (cv.name == bn) = true ↔ c.name = ConLeche.ofReduceBoolName :=
          beq_handle_iff hst3.wf hnmA3 d7
        rcases AM.ite_ok r7 with ⟨hy7, hg7⟩ | ⟨hn7, hg7⟩
        · -- an `ofReduce*` axiom
          have hor : c.name = ConLeche.ofReduceNatName ∨
              c.name = ConLeche.ofReduceBoolName := by
            rcases Bool.or_eq_true _ _ |>.mp hy7 with h | h
            · exact Or.inl (hrn.mp h)
            · exact Or.inr (hbn.mp h)
          obtain ⟨b8, s8, g8, r8⟩ := AM.bind_ok hg7
          obtain ⟨hst8, hx8, hc8, hp8, he8⟩ := ofReduceAxOk_run hok3 hcA3 g8
          rcases AM.ite_ok r8 with ⟨hy8, hg8⟩ | ⟨_, hbad8⟩
          · have hext : Ext s.store s8.store := hext02.trans hx8
            have hpins8 : s8.pins = s.pins := by rw [hp8, hpin02]
            have hpureR := checkDecl_axiom_ofReduce_pure (pinsP := pinsP) hnmP
              hpure2 hstdP htcP hor (he8 ▸ hy8)
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hg8
            exact ⟨hst8, hext, hpins8, ⟨.axiomInfo c :: env.consts, env.tables⟩, F2, hpureR⟩
          · exact absurd hbad8 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
        · -- neither: `propext`/`choice` decline, `sorryAx` skip, else decline
          have horP : ¬ (c.name = ConLeche.ofReduceNatName ∨
              c.name = ConLeche.ofReduceBoolName) := by
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
          have hpe : (cv.name == pe) = true ↔ c.name = ConLeche.propextName :=
            beq_handle_iff hst3.wf hnmA3 d9
          have hch : (cv.name == ch) = true ↔ c.name = ConLeche.choiceName :=
            beq_handle_iff hst3.wf hnmA3 d10
          rcases AM.ite_ok r10 with ⟨_, hbad10⟩ | ⟨hn10, hg10⟩
          · exact absurd hbad10 (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
          · have hstdShape : ¬ (c.name = ConLeche.propextName ∨
                c.name = ConLeche.choiceName) := by
              intro h
              refine hn10 ?_
              rcases h with h | h
              · exact Bool.or_eq_true _ _ |>.mpr (Or.inl (hpe.mpr h))
              · exact Bool.or_eq_true _ _ |>.mpr (Or.inr (hch.mpr h))
            obtain ⟨sa, s11, g11, r11⟩ := AM.bind_ok hg10
            obtain ⟨e11, d11⟩ :=
              pinAt_run (x := ConLeche.sorryAxName) hok3.check.pins rfl g11
            rw [e11] at r11
            have hsa : (cv.name == sa) = true ↔ c.name = ConLeche.sorryAxName :=
              beq_handle_iff hst3.wf hnmA3 d11
            rcases AM.ite_ok r11 with ⟨hy11, hg11⟩ | ⟨_, hbad11⟩
            · have hpureA := checkDecl_axiom_sorryAx_pure (pinsP := pinsP) hnmP
                hpure2 hstdP htcP horP hstdShape (hsa.mp hy11)
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hg11
              exact ⟨hst3, hext02, hpin02, env, F2, hpureA⟩
            · -- the decline reads the name back for its message, then fails
              exact absurd hbad11 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

