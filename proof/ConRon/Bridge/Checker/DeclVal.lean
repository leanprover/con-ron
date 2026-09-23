/-
# `ConRon.Bridge.Checker.DeclVal` — `DeclCheck`'s value checks and the three pin gates

`Arena/DeclCheck.lean` is the twin of `ConLeche/Kernel/DeclCheck.lean` plus the
three value-kind checks of `ConLeche/Kernel/Checker.lean:32-107`, and this
module is its bridge tier.  Four groups, and they are exactly the four things
`Bridge/Checker/Decl.lean`'s `defn` / `thm` / `opaque` arms call after
`checkConstantVal`:

1. **the three value checks** — `checkDefnVal`, `checkThmVal`,
   `checkOpaqueVal`.  Each is `installValue` plus one inference and one
   conversion, and each ends in an `IFEnv.push`, so each concludes `Pushed`
   and `Bridge/Checker/Inv.lean`'s **`StepOK env' fe' s'`** for the extended
   environment — the index answers, the environment is well formed, the index
   is its list's index, and it denotes.  Their state frame is `CoreStep` and
   not `StateOK` (task #97-P3-Checker-2): each CALLS the core, so the caches
   move, and what survives is the invariant at the environment the core ran at
   — which is the pre-insertion one, exactly as `checkConstantVal_bridge`
   concludes.  `StepOK` is what the two pin gates below read `fe2` for;
2. **the structural-`Nat` gate** — `natOpGuard` / `natOpStoredOkAll` /
   `certifyNatEqs`, run in the PRE-insertion environment with the operation's
   self-references replaced by its stored value;
3. **the `Nat.div`/`Nat.mod` variant gate** — `checkDivModPin`, whose loop is
   the one consumer of `Bridge/Checker/Base.lean`'s `orElseAttempt_run`;
4. **the compiler-trust gate** — `checkReducePin`.

**Why the pin gates are not `Bridge/Checker/Arms.lean`'s business.**  Each of
them runs AFTER the value check has already extended the environment, at the
extended index `fe2` and the pre-insertion one `fe` at once — con-leche's
`checkDivModPin ops pins env env2 c` and `checkReducePin ops env env2 c value`
take both for the same reason.  So each needs two invariants at once, which is
a shape nothing else in the tier has, and stating them here keeps the arms
uniform.

**What the second one is, corrected** (task #97-P3-Checker-2, named in task
#97-P3-Checker-3).  The round that stated these asked for
`FoldOK μ env2 fe2 s` — and `FoldOK` carries `PersIFEnv fe2`, which is
**false**: `fe2` is the environment the value check has just extended INSIDE
the per-declaration bracket, so the constant it holds carries a freshly
interned, hence scratch, type.  It is task #97-P3-Ind's finding at a second
site.  What the gates actually read `fe2` for is `reduceStoredOk fe2 c` /
`divModEnvGuard fe2 c`, two index lookups and no core call, so the clause they
need is **`StepOK env2 fe2 s`** — `Bridge/Checker/Inv.lean`'s name for exactly
that, and what the three value checks above now hand back.

**Both gates only ever DECLINE or pass.**  Neither installs anything: their
result is `Unit` on both sides, and the environment the arm returns is the one
the value check produced.  That is why their bridge theorems have no
environment clause at all — they are the cheapest statements of the tier and
the most expensive proofs, because the certificates they check are pinned
terms the core must run on.
-/
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Decl
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Core.Walks.Cached
import ConLeche.Verify.CheckerSplit
import ConLeche.Verify.Extend.Inversions

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## One fuel per arm

Each of the six is con-leche's own `*_datF` read through `FueledM`'s
monotonicity, exactly as `Bridge/Checker/Mono.lean`'s `checkDecl_mono` is: an
arm composes two or three of these and needs them all at one fuel. -/

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:857 checkDefnVal_datF. -/
theorem checkDefnVal_mono {μ : CheckMode} {env env' : Env} {c : ConstantVal}
    {x : Expr} {hint : ReducibilityHint} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkDefnVal (ConLeche.fueledOps μ F) env c x hint
      = .ok env') :
    ConLeche.checkDefnVal (ConLeche.fueledOps μ F') env c x hint = .ok env' := by
  rw [← ConLeche.checkDefnVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkDefnVal (ConLeche.fueledOpsM μ) env c x hint).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:864 checkThmVal_datF. -/
theorem checkThmVal_mono {μ : CheckMode} {env env' : Env} {c : ConstantVal}
    {x : Expr} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkThmVal (ConLeche.fueledOps μ F) env c x = .ok env') :
    ConLeche.checkThmVal (ConLeche.fueledOps μ F') env c x = .ok env' := by
  rw [← ConLeche.checkThmVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkThmVal (ConLeche.fueledOpsM μ) env c x).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:871 checkOpaqueVal_datF. -/
theorem checkOpaqueVal_mono {μ : CheckMode} {env env' : Env} {c : ConstantVal}
    {x : Expr} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env') :
    ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F') env c x = .ok env' := by
  rw [← ConLeche.checkOpaqueVal_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkOpaqueVal (ConLeche.fueledOpsM μ) env c x).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:878 certifyNatEqs_datF. -/
theorem certifyNatEqs_mono {μ : CheckMode} {env : Env}
    {xs : List (Expr × Expr)} {r : Bool} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env xs = .ok r) :
    ConLeche.certifyNatEqs (ConLeche.fueledOps μ F') env xs = .ok r := by
  rw [← ConLeche.certifyNatEqs_datF (mode := μ)] at h ⊢
  exact (ConLeche.certifyNatEqs (ConLeche.fueledOpsM μ) env xs).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:954 checkDivModPin_datF. -/
theorem checkDivModPin_mono {μ : CheckMode} {pinsP : List NatOpPinSet}
    {env env2 : Env} {nm : ConLeche.Name} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkDivModPin (ConLeche.fueledOps μ F) pinsP env env2 nm
      = .ok ()) :
    ConLeche.checkDivModPin (ConLeche.fueledOps μ F') pinsP env env2 nm
      = .ok () := by
  rw [← ConLeche.checkDivModPin_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkDivModPin (ConLeche.fueledOpsM μ) pinsP env env2 nm).property
    hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:965 checkReducePin_datF. -/
theorem checkReducePin_mono {μ : CheckMode} {env env2 : Env}
    {nm : ConLeche.Name} {x : Expr} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x
      = .ok ()) :
    ConLeche.checkReducePin (ConLeche.fueledOps μ F') env env2 nm x = .ok () := by
  rw [← ConLeche.checkReducePin_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkReducePin (ConLeche.fueledOpsM μ) env env2 nm x).property
    hle h

/-! ## The install half, moved down

`installValue_pure` and `installValue_bridge` were stated and proved in
`Bridge/Checker/Split.lean` (task #97-P3-Checker round 4), which is the WRONG
side of the import DAG for their first consumer: `Split.lean` imports
`Fold.lean` imports `Arms.lean` imports this module, so the three value checks
below — each of which BEGINS with `Arena.installValue` — could not see them.
They move here unchanged; `Split.lean` still reads them, transitively, for
`checkValueGroup_bridge` and `annotStep_bridge` (task #97-P3-Checker round 6). -/

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue — the
PURE half: five guards accepted means con-leche's install accepts with the
annotated value. -/
theorem installValue_pure {μ : CheckMode} {F : Nat} {env : Env}
    {c : ConstantVal} {x ty : Expr}
    (h5 : x.looseBVarsBounded 0 = true)
    (h6 : x.hasFvar = false)
    (h7 : ConLeche.annotateCore μ env F 0 x = .ok ty)
    (h8 : ty.allLevelParamsDefined c.levelParams = true)
    (h9 : ty.constsResolve env = true) :
    ConLeche.installValue (ConLeche.fueledOps μ F) env c x = .ok ty := by
  simp only [ConLeche.installValue, ConLeche.fueledOps, h5, h6, h7, h8, h9,
    Bool.false_eq_true, if_false, if_true, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue — the
value's guards and annotation.

**PROVED** (task #97-P3-Checker round 4): the last five steps of
`installConstantVal_bridge`, at the VALUE rather than the type —
`looseBVarsBoundedFast` and `hasFvarFast` (`Bridge/ExprOps/Walks.lean`),
`KnotSpec.annotate`, `allLevelParamsDefined_run` and
`constsResolveFFast_run`. -/
theorem installValue_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cv : IConstantVal} {c : ConstantVal} {value jv : EIdx} {x : Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (hck : CheckOK μ env fe s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : installValue μ fe cv value s = .ok (jv, s')) :
    CoreStep μ env fe s s' ∧ ∃ y F, denoteE s'.store jv = some y ∧
      ConLeche.installValue (ConLeche.fueledOps μ F) env c x = .ok y := by
  obtain ⟨hnm, hlps, -⟩ := denoteCV_inv hcv
  have hknot := hk.knot env fe henv
  have hck0 : CheckOK μ env fe s := hck
  have hnever : ∀ {α β γ : Type} {x : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (x >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.installValue] at hrun
  -- 1. the loose-bound-variable guard
  obtain ⟨b5, s5, g5r, r7⟩ := AM.bind_ok hrun
  obtain ⟨h5st, h5c, h5p, h5r⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t.store = s.store ∧ t.caches = s.caches ∧
      t.pins = s.pins ∧ RelV (Expr.looseBVarsBounded 0) s.store value r)
    rfl g5r (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s
      value hck0.state (by rw [hv]; rfl))
  obtain ⟨hlbb, r8⟩ := AM.dunless_ok hnever r7
  replace r8 := AM.pure_bind_ok r8
  have hlbbP : x.looseBVarsBounded 0 = true := by
    rw [← h5r x hv]; exact hlbb
  have hck5 : CheckOK μ env fe s5 :=
    hck0.mono ⟨by rw [h5st]; exact hck0.state.wf⟩ (by rw [h5st]; exact Ext.refl _)
      h5c h5p
  have hv5 : denoteE s5.store value = some x := by rw [h5st]; exact hv
  have hlps5 : Frontend.denoteNList s5.store.ns cv.levelParams
      = some c.levelParams := by rw [h5st]; exact hlps
  -- 2. the free-variable guard
  obtain ⟨b6, s6, g6r, r9⟩ := AM.bind_ok r8
  obtain ⟨h6st, h6c, h6p, h6r⟩ := AM.of_run (P := fun t => t = s5)
    (Q := fun r t => t.store = s5.store ∧ t.caches = s5.caches ∧
      t.pins = s5.pins ∧ RelV Expr.hasFvar s5.store value r)
    rfl g6r (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s5 value
      hck5.state (by rw [hv5]; rfl))
  obtain ⟨hfv, r10⟩ := AM.dguard_ok hnever r9
  replace r10 := AM.pure_bind_ok r10
  have hfvP : x.hasFvar = false := by
    rw [← h6r x hv5]
    cases hb : b6 with
    | false => rfl
    | true => rw [hb] at hfv; exact absurd rfl hfv
  have hck6 : CheckOK μ env fe s6 :=
    hck5.mono ⟨by rw [h6st]; exact hck5.state.wf⟩ (by rw [h6st]; exact Ext.refl _)
      h6c h6p
  have hv6 : denoteE s6.store value = some x := by rw [h6st]; exact hv5
  have hlps6 : Frontend.denoteNList s6.store.ns cv.levelParams
      = some c.levelParams := by rw [h6st]; exact hlps5
  have hws : Expr.WScoped 0 x := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  -- 3. the annotation
  obtain ⟨jv2, s7, g7r, r11⟩ := AM.bind_ok r10
  obtain ⟨hck7, hx7, hp7, hsim7⟩ := AM.of_run (P := fun t => t = s6)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s6.store t.store ∧
      t.pins = s6.pins ∧
      Core.SimE (ConLeche.annotateCore μ env) 0 x t.store r)
    rfl g7r (hknot.annotate s6 0 value x hck6 hv6 hws)
  obtain ⟨w, hw7, hwsw, F7, hF7⟩ := hsim7
  have hlps7 : Frontend.denoteNList s7.store.ns cv.levelParams
      = some c.levelParams := denoteNList_ext hx7.lss.ls.ns _ _ hlps6
  -- 4. the undeclared-universe-parameter guard
  obtain ⟨b8, s8, g8r, r12⟩ := AM.bind_ok r11
  obtain ⟨h8st, h8c, h8p, h8r⟩ :=
    allLevelParamsDefined_run hck7.state hlps7 hw7 g8r
  obtain ⟨hlpd, r13⟩ := AM.dunless_ok hnever r12
  replace r13 := AM.pure_bind_ok r13
  have hlpdP : w.allLevelParamsDefined c.levelParams = true := by
    rw [← h8r]; exact hlpd
  have hck8 : CheckOK μ env fe s8 :=
    hck7.mono ⟨by rw [h8st]; exact hck7.state.wf⟩ (by rw [h8st]; exact Ext.refl _)
      h8c h8p
  have hw8 : denoteE s8.store jv2 = some w := by rw [h8st]; exact hw7
  -- 5. the unresolved-constant guard
  obtain ⟨b9, s9, g9r, r14⟩ := AM.bind_ok r13
  obtain ⟨h9st, h9c, h9p, h9r⟩ :=
    constsResolveFFast_run hck8 hw8 g9r
  obtain ⟨hcr, r15⟩ := AM.dunless_ok
    (AM.Never.bind fun _ => AM.Never.bind fun _ => AM.Never.fail_any) r14
  replace r15 := AM.pure_bind_ok r15
  have hcrP : w.constsResolve env = true := by rw [← h9r]; exact hcr
  have hck9 : CheckOK μ env fe s9 :=
    hck8.mono ⟨by rw [h9st]; exact hck8.state.wf⟩ (by rw [h9st]; exact Ext.refl _)
      h9c h9p
  have hw9 : denoteE s9.store jv2 = some w := by rw [h9st]; exact hw8
  -- 6. the answer
  obtain ⟨hjv, hs'⟩ := AM.pure_ok r15
  subst hjv
  subst hs'
  have hext : Ext s.store s'.store := by
    rw [← h5st, ← h6st]
    refine hx7.trans ?_
    rw [← h8st, ← h9st]
    exact Ext.refl _
  have hpins : s'.pins = s.pins := by rw [h9p, h8p, hp7, h6p, h5p]
  exact ⟨⟨hck9, hext, hpins⟩, ⟨w, F7, hw9,
    installValue_pure hlbbP hfvP hF7 hlpdP hcrP⟩⟩

/-! ## `ConstWF`, and what the guards already establish

**Round 5's scheduling finding, discharged.**  Each of the three value checks
ends in `IFEnv.push` and so concludes `StepOK env' fe' s'`, whose `envWF`
clause is `EnvWF ⟨c :: env.consts⟩` — and *con-leche does not prove that
`checkDefnVal` preserves `EnvWF`*: `Verify/BridgeWfImp.lean`'s
`checkDefnVal_wfimp` is about the fuel family, and the model tier takes
`EnvWF` as a hypothesis (`EnvModelM.toEnvFacts.wf`) rather than
re-establishing it.  What it DOES have, in `Verify/EnvWF.lean`, is
`EnvWF.cons` — so the debt is exactly `ConstWF ⟨c :: env.consts⟩ c`, and it is
one lemma shared by all three arms and by `Arena.checkDeclStep_bridge`'s fold
(`Bridge/Checker/Inv.lean`'s `StepOK.push`).

`ConstWF` splits in two along the constructor:

* **the four TYPE clauses**, which `checkDefnVal` never looks at — the value
  checks run at an ALREADY CHECKED header — so they are a *hypothesis*,
  `CVTypeWF`, discharged at every call site by `checkConstantVal_typeWF` from
  the front door's own pure run.  This is round 4's `PinsOK` and round 5's
  `hwsty`/`hwsjv` precedent: a missing precondition, repaired in place;
* **the four VALUE clauses**, which `installValue` DOES check — two directly
  (`allLevelParamsDefined`, `constsResolve`) and two at the RAW value, which
  `annotateCore` then preserves (`annotateCore_looseBVars`,
  `annotateCore_WScoped`).  That is `installValue_valueWF`, and it is
  con-leche's own `installValue_inv` plus two `Verify/Abstract.lean` lemmas.

`.thmInfo` and `.axiomInfo` need only the type half: `ConstWF` gives a
theorem's stored value no clause at all (it is opaque to reduction and stored
by its statement) and an `axiomInfo` has no value.  So the SAME hypothesis
serves all three, and only the `defn` arm spends the value half.

**What con-leche could carry instead** (for the pin's next bump).  Two of the
three pieces exist upstream but are `private`:
`Verify/Cached/BridgeCS4.lean`'s `cvA_type_facts'` is `checkConstantVal_typeWF`
letter for letter, and `constWF_intro'` beside it is the introduction the
three `constWF_*` below re-spell.  Making those two public — or, better,
putting `checkDefnVal_envWF` / `checkThmVal_envWF` / `checkOpaqueVal_envWF`
into `Verify/CheckerSplit.lean` beside `checkDefnVal_of_facts` — would retire
this whole section. -/

/-- con-leche: ConLeche/Verify/EnvWF.lean:147 ConstWF — **the four clauses
`ConstWF` asks of a constant's TYPE**, named so that the three value checks
can take one hypothesis instead of four.  `ConstWF env (.axiomInfo cv)` is
this and nothing else; the other constructors add their own clauses on top. -/
structure CVTypeWF (env : Env) (cv : ConstantVal) : Prop where
  fvar : cv.type.hasFvar = false
  lvls : cv.type.allLevelParamsDefined cv.levelParams = true
  res : cv.type.constsResolve env = true
  bnd : cv.type.looseBVarsBounded 0 = true

/-- con-leche: ConLeche/Verify/EnvWF.lean:304 Expr.constsResolve_mono — the
only clause that mentions the environment is monotone under a cons. -/
theorem CVTypeWF.cons {env : Env} {cv : ConstantVal} {c : ConstantInfo}
    (h : CVTypeWF env cv) : CVTypeWF ⟨c :: env.consts⟩ cv where
  fvar := h.fvar
  lvls := h.lvls
  res := ConLeche.Expr.constsResolve_mono h.res
  bnd := h.bnd

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:131 cvA_type_facts'
(private there) — **the four type clauses of a CHECKED constant**, off
con-leche's own `checkConstantVal_inv`: two of the four are guards on the raw
type and `annotateCore` preserves both (`annotateCore_looseBVars`, and
`annotateCore_WScoped` through `fvarsBelow 0`), the other two are tested on
the annotation itself. -/
theorem checkConstantVal_typeWF {μ : CheckMode} {F : Nat} {env : Env}
    {cv cvA : ConstantVal}
    (h : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cv = .ok cvA) :
    CVTypeWF env cvA := by
  obtain ⟨-, -, -, -, hlbt, hitf, type, stype, u, hann, htp, htr, -, -, rfl⟩ :=
    ConLeche.checkConstantVal_inv h
  exact { fvar := ConLeche.Expr.not_hasFvar_of_fvarsBelow_zero
            ((ConLeche.annotateCore_WScoped F cv.type hann
              (ConLeche.Expr.WScoped.of_not_hasFvar hitf)).fvarsBelow)
          lvls := htp
          res := htr
          bnd := ConLeche.annotateCore_looseBVars F cv.type hann hlbt }

/-- con-leche: ConLeche/Verify/CheckerSplit.lean:102 installValue_inv —
**the four `ConstWF` VALUE clauses of an installed value**, by the same
argument at the value instead of at the type. -/
theorem installValue_valueWF {μ : CheckMode} {F : Nat} {env : Env}
    {cv : ConstantVal} {x y : Expr}
    (h : ConLeche.installValue (ConLeche.fueledOps μ F) env cv x = .ok y) :
    y.hasFvar = false ∧ y.allLevelParamsDefined cv.levelParams = true ∧
      y.constsResolve env = true ∧ y.looseBVarsBounded 0 = true := by
  obtain ⟨hlb, hif, hann, hvp, hvr⟩ := ConLeche.installValue_inv h
  refine ⟨?_, hvp, hvr, ConLeche.annotateCore_looseBVars F x hann hlb⟩
  exact ConLeche.Expr.not_hasFvar_of_fvarsBelow_zero
    ((ConLeche.annotateCore_WScoped F x hann
      (ConLeche.Expr.WScoped.of_not_hasFvar hif)).fvarsBelow)

/-- con-leche: ConLeche/Verify/EnvWF.lean:147 ConstWF — the `defnInfo`
introduction: the type clauses, the value clauses, and five vacuous ones. -/
theorem constWF_defnInfo {env : Env} {cv : ConstantVal} {v : Expr}
    {hint : ReducibilityHint} (ht : CVTypeWF env cv)
    (g1 : v.hasFvar = false)
    (g2 : v.allLevelParamsDefined cv.levelParams = true)
    (g3 : v.constsResolve env = true)
    (g4 : v.looseBVarsBounded 0 = true) :
    ConLeche.ConstWF env (.defnInfo cv v hint) :=
  ⟨ht.fvar, ht.lvls, ht.res, ht.bnd,
   fun _ _ _ heq => by
     obtain ⟨rfl, rfl, rfl⟩ := ConLeche.ConstantInfo.defnInfo.inj heq
     exact ⟨g1, g2, g3, g4⟩,
   fun _ _ _ _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ _ heq => ConLeche.ConstantInfo.noConfusion heq⟩

/-- con-leche: ConLeche/Verify/EnvWF.lean:147 ConstWF — the `thmInfo`
introduction.  **A theorem's stored value carries no clause**: it is the
record's RAW value, opaque to reduction and never read by the kernel or by the
invariant, so the type half is the whole of it. -/
theorem constWF_thmInfo {env : Env} {cv : ConstantVal} {v : Expr}
    (ht : CVTypeWF env cv) : ConLeche.ConstWF env (.thmInfo cv v) :=
  ⟨ht.fvar, ht.lvls, ht.res, ht.bnd,
   fun _ _ _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ _ _ _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ _ heq => ConLeche.ConstantInfo.noConfusion heq⟩

/-- con-leche: ConLeche/Verify/EnvWF.lean:147 ConstWF — the `axiomInfo`
introduction, which an `opaque` install is stored as: no value at all. -/
theorem constWF_axiomInfo {env : Env} {cv : ConstantVal}
    (ht : CVTypeWF env cv) : ConLeche.ConstWF env (.axiomInfo cv) :=
  ⟨ht.fvar, ht.lvls, ht.res, ht.bnd,
   fun _ _ _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ _ _ _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ heq => ConLeche.ConstantInfo.noConfusion heq,
   fun _ _ heq => ConLeche.ConstantInfo.noConfusion heq⟩

/-! ## The three value checks -/

/-- con-leche: ConLeche/Kernel/Checker.lean:32-50 checkDefnVal — a
definition's value against its checked constant, returning the pushed index.

**PROVED** (task #97-P3-Checker round 6): `installValue_bridge`, one
`KnotSpec.infer`, one `KnotSpec.defeq`, then `StepOK.push`.

**The statement gained `htw : CVTypeWF env c`.**  `StepOK` carries
`EnvWF ⟨.defnInfo c y hint :: env.consts⟩`, hence
`ConstWF … (.defnInfo c y hint)`, hence the four clauses about `c.type` — and
`checkDefnVal` never looks at the type: the value checks run at an ALREADY
CHECKED header, whose guards are `checkConstantVal`'s.  Nothing in the
round-1 hypotheses delivers them (`FoldOK` speaks about `env`, and the
statement does not say `c` is a constant OF `env`), so as stated the theorem
was not provable.  It is free at the one call site —
`Bridge/Checker/Arms.lean`'s `defn` arm has `checkConstantVal_bridge`'s own
pure run, and `checkConstantVal_typeWF` reads it off.  Round 4's `PinsOK` and
round 5's `hwsty`/`hwsjv` precedent: a missing precondition, repaired in
place. -/
theorem checkDefnVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {hint : ReducibilityHint} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (htw : CVTypeWF env c)
    (hv : denoteE s.store value = some x)
    (hrun : checkDefnVal μ fe cv value hint s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧ Pushed fe fe' ∧
      ∃ env' F, StepOK env' fe' s' ∧
        ConLeche.checkDefnVal (ConLeche.fueledOps μ F) env c x hint = .ok env' := by
  have hknot := hk.knot env fe hok.envWF
  have hnever : ∀ {α β γ : Type} {z : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (z >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.checkDefnVal] at hrun
  -- 1. the install half
  obtain ⟨jv, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, y, F1, hy1, hIV⟩ := installValue_bridge hμ hk hok.envWF hok.check hcv hv g1
  obtain ⟨gf, gl, gr, gb⟩ := installValue_valueWF hIV
  have hwsy : ConLeche.Expr.WScoped 0 y :=
    ConLeche.Expr.WScoped.of_not_hasFvar gf
  -- 2. the inference
  obtain ⟨vtype, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hck2, hx2, hp2, hsim2⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s1.store t.store ∧
      t.pins = s1.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 y t.store r)
    rfl g2 (hknot.infer s1 0 jv y hstep1.ok hy1 hwsy)
  obtain ⟨vt, hvt2, hwsvt, F2, hF2⟩ := hsim2
  -- 3. the conversion
  have hcv2 : Frontend.denoteCV s2.store cv = some c :=
    denoteCV_ext hcv (hstep1.ext.trans hx2)
  obtain ⟨-, -, hty2⟩ := denoteCV_inv hcv2
  obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hck3, hx3, hp3, hsim3⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s2.store t.store ∧
      t.pins = s2.pins ∧
      Core.SimV (ConLeche.isDefEqCore μ env) 0 vt c.type r)
    rfl g3 (hknot.defeq s2 0 vtype cv.type vt c.type hck2 hvt2 hty2 hwsvt
      (ConLeche.Expr.WScoped.of_not_hasFvar htw.fvar))
  obtain ⟨F3, hF3⟩ := hsim3
  obtain ⟨hb, r4⟩ := AM.dunless_ok hnever r3
  replace r4 := AM.pure_bind_ok r4
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
  subst hb
  -- 4. the answer
  have hext : Ext s.store s'.store := hstep1.ext.trans (hx2.trans hx3)
  have hcv3 : Frontend.denoteCV s'.store cv = some c := denoteCV_ext hcv2 hx3
  have hy3 : denoteE s'.store jv = some y := denote_ext (denote_ext hy1 hx2) hx3
  have hci3 : Frontend.denoteCI s'.store (.defnInfo cv jv hint)
      = some (.defnInfo c y hint) := by
    simp only [Frontend.denoteCI, hcv3, hy3]
  refine ⟨⟨hck3, hext, by rw [hp3, hp2, hstep1.pins]⟩, Pushed.push fe _,
    ⟨.defnInfo c y hint :: env.consts⟩, max F1 (max F2 F3), ?_, ?_⟩
  · exact (hok.toStepOK.mono hext).push hck3.state
      (fun t hq => IConstantInfo.noConfusion hq) hci3
      (constWF_defnInfo htw.cons gf gl
        (ConLeche.Expr.constsResolve_mono gr) gb)
  · obtain ⟨hlb, hif, hann, hvp, hvr⟩ := ConLeche.installValue_inv
      (ConLeche.installValue_mono (by omega : F1 ≤ max F1 (max F2 F3)) hIV)
    exact ConLeche.checkDefnVal_of_facts hlb hif hann hvp hvr
      (ConLeche.inferTypeCore_mono (by omega) hF2)
      (ConLeche.isDefEqCore_mono (by omega) hF3)

/-- con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal — **a theorem is
stored by its statement**: the constant keeps the record's RAW value as an
unread datum and the annotated value is a witness, checked and discarded.

**PROVED** (task #97-P3-Checker round 6): the widest of the three, because
the is-a-proposition test is three steps the other two do not have —
`EnsureSortSpec`, the pinned `zeroLevel` (`pinZeroLevel_spec`) and
`lvlEq?_spec`, whose verdict IS `Level.isEquiv` at the two handles'
denotations, read at BOTH signs (the `none` case is `liftFueled`'s failure and
cannot occur on a successful run).  It gains the same `htw` as the other two —
and here it is spent twice, once for `WScoped 0 c.type` at the FIRST
inference (which the other two do not make) and once at the conversion.

**The stored value is `x`, not the witness.**  `ConstWF` gives a theorem's
value no clause, so `constWF_thmInfo` is the type half alone and the annotated
`y` never reaches the environment — exactly con-leche's own reading. -/
theorem checkThmVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (htw : CVTypeWF env c)
    (hv : denoteE s.store value = some x)
    (hrun : checkThmVal μ fe cv value s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧ Pushed fe fe' ∧
      ∃ env' F, StepOK env' fe' s' ∧
        ConLeche.checkThmVal (ConLeche.fueledOps μ F) env c x = .ok env' := by
  have hknot := hk.knot env fe hok.envWF
  have hsortS := hk.sort env fe hok.envWF
  have hwsty : ConLeche.Expr.WScoped 0 c.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar htw.fvar
  have hnever : ∀ {α β γ : Type} {z : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (z >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  obtain ⟨-, -, hty0⟩ := denoteCV_inv hcv
  simp only [Arena.checkThmVal, Arena.zeroLevel] at hrun
  -- 1. the type's own inference
  obtain ⟨stype, s1, ga, ra⟩ := AM.bind_ok hrun
  obtain ⟨hcka, hxa, hpa, hsima⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s.store t.store ∧
      t.pins = s.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 c.type t.store r)
    rfl ga (hknot.infer s 0 cv.type c.type hok.check hty0 hwsty)
  obtain ⟨sty, hsty, hwssty, Fa, hFa⟩ := hsima
  -- 2. the sort
  obtain ⟨u, s2, gb, rb⟩ := AM.bind_ok ra
  obtain ⟨hckb, hxb, hpb, hsimb⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s1.store t.store ∧
      t.pins = s1.pins ∧
      SimL (ConLeche.ensureSortCore μ env) 0 sty t.store r)
    rfl gb (hsortS s1 0 stype sty hcka hsty hwssty)
  obtain ⟨uu, huu, Fb, hFb⟩ := hsimb
  -- 3. the pinned zero level — a pin read moves nothing
  obtain ⟨z, s3, gc, rc⟩ := AM.bind_ok rb
  obtain ⟨hs3, hz⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => t = s2 ∧ denoteL s2.store.ls r = some .zero)
    rfl gc (pinZeroLevel_spec s2 hckb.pins)
  rw [hs3] at rc
  -- 4. the level comparison: the verdict IS `Level.isEquiv` at the denotations
  obtain ⟨o, s4, gd, rd⟩ := AM.bind_ok rc
  obtain ⟨hckd, hstd, hpd, lu, lv, hlu, hlv, hod⟩ := AM.of_run
    (P := fun t => t = s2)
    (Q := fun r t => CheckOK μ env fe t ∧ t.store = s2.store ∧
      t.pins = s2.pins ∧ ∃ lu lv, denoteL s2.store.ls u = some lu ∧
        denoteL s2.store.ls z = some lv ∧ r = ConLeche.Level.isEquiv lu lv)
    rfl gd (Core.lvlEq?_spec s2 u z hckb)
  rw [Option.some.inj (hlu.symm.trans huu),
    Option.some.inj (hlv.symm.trans hz)] at hod
  -- 5. the fuel lift, and the is-a-proposition guard
  obtain ⟨b5, s5, ge, re⟩ := AM.bind_ok rd
  obtain ⟨bb, rfl⟩ : ∃ bb, o = some bb := by
    cases ho : o with
    | none => rw [ho] at ge; exact absurd ge (AM.Never.fail _ _ _ _)
    | some bb => exact ⟨bb, rfl⟩
  obtain ⟨rfl, rfl⟩ := AM.pure_ok ge
  obtain ⟨hprop, rf⟩ := AM.dunless_ok hnever re
  replace rf := AM.pure_bind_ok rf
  have heqv : ConLeche.Level.isEquiv uu .zero = some true := by
    rw [← hod, hprop]
  -- 6. the install half
  have hext4 : Ext s.store s5.store := by rw [hstd]; exact hxa.trans hxb
  have hpin4 : s5.pins = s.pins := by rw [hpd, hpb, hpa]
  have hv4 : denoteE s5.store value = some x := denote_ext hv hext4
  have hcv4 : Frontend.denoteCV s5.store cv = some c := denoteCV_ext hcv hext4
  obtain ⟨jv, s6, gf, rg⟩ := AM.bind_ok rf
  obtain ⟨hstep6, y, F1, hy6, hIV⟩ :=
    installValue_bridge hμ hk hok.envWF hckd hcv4 hv4 gf
  obtain ⟨gfv, glv, grv, gbv⟩ := installValue_valueWF hIV
  have hwsy : ConLeche.Expr.WScoped 0 y :=
    ConLeche.Expr.WScoped.of_not_hasFvar gfv
  -- 7. the witness's inference
  obtain ⟨vtype, s7, gg, rh⟩ := AM.bind_ok rg
  obtain ⟨hck7, hx7, hp7, hsim7⟩ := AM.of_run (P := fun t => t = s6)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s6.store t.store ∧
      t.pins = s6.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 y t.store r)
    rfl gg (hknot.infer s6 0 jv y hstep6.ok hy6 hwsy)
  obtain ⟨vt, hvt7, hwsvt, F2, hF2⟩ := hsim7
  -- 8. the conversion
  have hcv7 : Frontend.denoteCV s7.store cv = some c :=
    denoteCV_ext hcv4 (hstep6.ext.trans hx7)
  obtain ⟨-, -, hty7⟩ := denoteCV_inv hcv7
  obtain ⟨b8, s8, gi, ri⟩ := AM.bind_ok rh
  obtain ⟨hck8, hx8, hp8, hsim8⟩ := AM.of_run (P := fun t => t = s7)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s7.store t.store ∧
      t.pins = s7.pins ∧
      Core.SimV (ConLeche.isDefEqCore μ env) 0 vt c.type r)
    rfl gi (hknot.defeq s7 0 vtype cv.type vt c.type hck7 hvt7 hty7 hwsvt hwsty)
  obtain ⟨F3, hF3⟩ := hsim8
  obtain ⟨hb, rj⟩ := AM.dunless_ok hnever ri
  replace rj := AM.pure_bind_ok rj
  obtain ⟨rfl, rfl⟩ := AM.pure_ok rj
  subst hb
  -- 9. the answer
  have hext : Ext s.store s'.store :=
    hext4.trans (hstep6.ext.trans (hx7.trans hx8))
  have hcv8 : Frontend.denoteCV s'.store cv = some c := denoteCV_ext hcv7 hx8
  have hx8v : denoteE s'.store value = some x := denote_ext hv hext
  have hci8 : Frontend.denoteCI s'.store (.thmInfo cv value)
      = some (.thmInfo c x) := by
    simp only [Frontend.denoteCI, hcv8, hx8v]
  refine ⟨⟨hck8, hext, by rw [hp8, hp7, hstep6.pins, hpin4]⟩,
    Pushed.push fe _, ⟨.thmInfo c x :: env.consts⟩,
    max (max Fa Fb) (max F1 (max F2 F3)), ?_, ?_⟩
  · exact (hok.toStepOK.mono hext).push hck8.state
      (fun t hq => IConstantInfo.noConfusion hq) hci8
      (constWF_thmInfo htw.cons)
  · obtain ⟨hlb, hif, hann, hvp, hvr⟩ := ConLeche.installValue_inv
      (ConLeche.installValue_mono
        (by omega : F1 ≤ max (max Fa Fb) (max F1 (max F2 F3))) hIV)
    exact ConLeche.checkThmVal_of_facts
      (ConLeche.inferTypeCore_mono (by omega) hFa)
      (ConLeche.ensureSortCore_mono (by omega) hFb)
      heqv hlb hif hann hvp hvr
      (ConLeche.inferTypeCore_mono (by omega) hF2)
      (ConLeche.isDefEqCore_mono (by omega) hF3)

/-- con-leche: ConLeche/Kernel/Checker.lean:84-107 checkOpaqueVal — the
theorem check without the is-a-proposition requirement; the result is stored
as an `axiomInfo`.

**PROVED** (task #97-P3-Checker round 6): `checkDefnVal_bridge`'s proof, word
for word, with `.axiomInfo` in place of `.defnInfo` — and the `ConstWF`
introduction is the cheaper one, because an `axiomInfo` has no value clause at
all (the checked value is a realizability witness, consumed by the model
extension and then discarded).  It gains the same `htw`. -/
theorem checkOpaqueVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (htw : CVTypeWF env c)
    (hv : denoteE s.store value = some x)
    (hrun : checkOpaqueVal μ fe cv value s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧ Pushed fe fe' ∧
      ∃ env' F, StepOK env' fe' s' ∧
        ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env' := by
  have hknot := hk.knot env fe hok.envWF
  have hnever : ∀ {α β γ : Type} {z : AM α} {f : α → Arena.CheckError}
      {g : γ → AM β}, AM.Never (z >>= fun a => ((Arena.fail (f a) : AM γ) >>= g)) :=
    fun {_ _ _ _ _ _} => AM.Never.bind fun _ => AM.Never.fail_any
  simp only [Arena.checkOpaqueVal] at hrun
  obtain ⟨jv, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, y, F1, hy1, hIV⟩ := installValue_bridge hμ hk hok.envWF hok.check hcv hv g1
  obtain ⟨gf, gl, gr, gb⟩ := installValue_valueWF hIV
  have hwsy : ConLeche.Expr.WScoped 0 y :=
    ConLeche.Expr.WScoped.of_not_hasFvar gf
  obtain ⟨vtype, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hck2, hx2, hp2, hsim2⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s1.store t.store ∧
      t.pins = s1.pins ∧
      Core.SimE (ConLeche.inferTypeCore μ env) 0 y t.store r)
    rfl g2 (hknot.infer s1 0 jv y hstep1.ok hy1 hwsy)
  obtain ⟨vt, hvt2, hwsvt, F2, hF2⟩ := hsim2
  have hcv2 : Frontend.denoteCV s2.store cv = some c :=
    denoteCV_ext hcv (hstep1.ext.trans hx2)
  obtain ⟨-, -, hty2⟩ := denoteCV_inv hcv2
  obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hck3, hx3, hp3, hsim3⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s2.store t.store ∧
      t.pins = s2.pins ∧
      Core.SimV (ConLeche.isDefEqCore μ env) 0 vt c.type r)
    rfl g3 (hknot.defeq s2 0 vtype cv.type vt c.type hck2 hvt2 hty2 hwsvt
      (ConLeche.Expr.WScoped.of_not_hasFvar htw.fvar))
  obtain ⟨F3, hF3⟩ := hsim3
  obtain ⟨hb, r4⟩ := AM.dunless_ok hnever r3
  replace r4 := AM.pure_bind_ok r4
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
  subst hb
  have hext : Ext s.store s'.store := hstep1.ext.trans (hx2.trans hx3)
  have hcv3 : Frontend.denoteCV s'.store cv = some c := denoteCV_ext hcv2 hx3
  have hci3 : Frontend.denoteCI s'.store (.axiomInfo cv)
      = some (.axiomInfo c) := by
    simp only [Frontend.denoteCI, hcv3, Option.map_some]
  refine ⟨⟨hck3, hext, by rw [hp3, hp2, hstep1.pins]⟩, Pushed.push fe _,
    ⟨.axiomInfo c :: env.consts⟩, max F1 (max F2 F3), ?_, ?_⟩
  · exact (hok.toStepOK.mono hext).push hck3.state
      (fun t hq => IConstantInfo.noConfusion hq) hci3
      (constWF_axiomInfo htw.cons)
  · obtain ⟨hlb, hif, hann, hvp, hvr⟩ := ConLeche.installValue_inv
      (ConLeche.installValue_mono (by omega : F1 ≤ max F1 (max F2 F3)) hIV)
    exact ConLeche.checkOpaqueVal_of_facts hlb hif hann hvp hvr
      (ConLeche.inferTypeCore_mono (by omega) hF2)
      (ConLeche.isDefEqCore_mono (by omega) hF3)

/-! ## The structural-`Nat` gate

Six readers and one certifier.  None of the six calls the core — they read the
environment index and intern pinned literals — so each has `PinStep`'s frame
and an answer relation, and the certifier alone is a `CoreStep`. -/

/-- con-leche: none — a list of equation PAIRS denotes, pointwise.  The
`certifyNatEqs` chain is stated with it rather than with the membership shape
the round that stated it used, because the recursion is positional: the arena
certifies the `i`-th pair against con-leche's `i`-th (task
#97-P3-Checker-2). -/
def EqPairsDenote (st : EStore) :
    List (EIdx × EIdx) → List (Expr × Expr) → Prop
  | [], [] => True
  | p :: ps, q :: qs =>
    denoteE st p.1 = some q.1 ∧ denoteE st p.2 = some q.2 ∧
      EqPairsDenote st ps qs
  | _, _ => False

/-- con-leche: none — the pairing survives an arena extension; `denote_ext`
at each of the two components. -/
theorem EqPairsDenote.mono {st st' : EStore} (hx : Ext st st') :
    ∀ {ps : List (EIdx × EIdx)} {qs : List (Expr × Expr)},
      EqPairsDenote st ps qs → EqPairsDenote st' ps qs := by
  intro ps
  induction ps with
  | nil =>
    intro qs h
    cases qs with
    | nil => exact h
    | cons q qs => exact absurd h (by simp [EqPairsDenote])
  | cons p ps ih =>
    intro qs h
    cases qs with
    | nil => exact absurd h (by simp [EqPairsDenote])
    | cons q qs =>
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨denote_ext h1 hx, denote_ext h2 hx, ih h3⟩

/-- con-leche: ConLeche/Kernel/Checker.lean:110-125 certifyNatEqs — the cons
step, on the pure side: an accepted head and an accepted tail are an accepted
list, at ONE fuel. -/
theorem certifyNatEqs_cons_pure {μ : CheckMode} {env : Env} {F : Nat}
    {q : Expr × Expr} {qs : List (Expr × Expr)}
    (h1 : (ConLeche.fueledOps μ F).isDefEq env 2 q.1 q.2 = .ok true)
    (h2 : ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env qs = .ok true) :
    ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env (q :: qs) = .ok true := by
  simp only [ConLeche.certifyNatEqs, h1, h2, if_true, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:475-481 natOpNames — the seven
structural fast-path operations, off the pin table.

**PROVED** (task #97-P3-Checker-3): seven `pinAt_run`s, in
`reservedBasisNames_run`'s shape and under its rule — the seven facts are
carried separately and the list is assembled once, at the end, against the
literal the `do`-block returns.  A pin read leaves the state alone, so there
is nothing to transport and the frame is an equation. -/
theorem natOpNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : natOpNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natOpNames := by
  simp only [Arena.natOpNames] at hr
  obtain ⟨n1, t1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.natPredName) hp rfl g1
  rw [e1] at r1
  obtain ⟨n2, t2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.natAddName) hp rfl g2
  rw [e2] at r2
  obtain ⟨n3, t3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨e3, d3⟩ := pinAt_run (x := ConLeche.natSubName) hp rfl g3
  rw [e3] at r3
  obtain ⟨n4, t4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.natMulName) hp rfl g4
  rw [e4] at r4
  obtain ⟨n5, t5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.natPowName) hp rfl g5
  rw [e5] at r5
  obtain ⟨n6, t6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.natBeqName) hp rfl g6
  rw [e6] at r6
  obtain ⟨n7, t7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.natBleName) hp rfl g7
  rw [e7] at r7
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r7
  exact ⟨rfl, d1, d2, d3, d4, d5, d6, d7, trivial⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:483-498 natDivModNames — the
eight WF-recursive operations, off the pin table.

**PROVED** (task #97-P3-Checker-3): `natOpNames_run`'s proof, one slot
longer. -/
theorem natDivModNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : natDivModNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natDivModNames := by
  simp only [Arena.natDivModNames] at hr
  obtain ⟨n1, t1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.natDivName) hp rfl g1
  rw [e1] at r1
  obtain ⟨n2, t2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨e2, d2⟩ := pinAt_run (x := ConLeche.natModName) hp rfl g2
  rw [e2] at r2
  obtain ⟨n3, t3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨e3, d3⟩ := pinAt_run (x := ConLeche.natGcdName) hp rfl g3
  rw [e3] at r3
  obtain ⟨n4, t4, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.natLandName) hp rfl g4
  rw [e4] at r4
  obtain ⟨n5, t5, g5, r5⟩ := AM.bind_ok r4
  obtain ⟨e5, d5⟩ := pinAt_run (x := ConLeche.natLorName) hp rfl g5
  rw [e5] at r5
  obtain ⟨n6, t6, g6, r6⟩ := AM.bind_ok r5
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.natXorName) hp rfl g6
  rw [e6] at r6
  obtain ⟨n7, t7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp rfl g7
  rw [e7] at r7
  obtain ⟨n8, t8, g8, r8⟩ := AM.bind_ok r7
  obtain ⟨e8, d8⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp rfl g8
  rw [e8] at r8
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r8
  exact ⟨rfl, d1, d2, d3, d4, d5, d6, d7, d8, trivial⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:500-523 natOpDeps — the
operations (transitively) involved in `c`'s recurrences.  The twin's dispatch
is a chain of HANDLE comparisons where con-leche's is a chain of name
comparisons, so the answer is exact for `denoteN_inj`'s reason.

**PROVED** (task #97-P3-Checker-3): fifteen `pinAt_run`s, `beq_handle_iff` at
each of the fifteen tests, and the sixteen arms.  A pin read leaves the state
alone, so every arm's frame is the same `rfl`-shaped record and the only
content is which list comes out.

**The statement gained `PinsOK s`** — it read the pin table fifteen times and
did not ask for it, so as stated it was not provable (nothing made the handles
`pinAt` hands back denote anything).  It is free at the one call site
(`Bridge/Checker/Arms.lean`'s `defn` arm has `FoldOK`, hence
`hok.check.pins`). -/
theorem natOpDeps_run {cn : NIdx} {nm : ConLeche.Name} {ds : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpDeps cn s = .ok (ds, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ denoteNL s'.store ds (ConLeche.natOpDeps nm) := by
  simp only [Arena.natOpDeps] at hr
  -- fifteen pin reads; none of them moves the state
  obtain ⟨hpr, u0, q0, w0⟩ := AM.bind_ok hr
  obtain ⟨p0, d0⟩ := pinAt_run (x := ConLeche.natPredName) hp rfl q0
  rw [p0] at w0
  obtain ⟨had, u1, q1, w1⟩ := AM.bind_ok w0
  obtain ⟨p1, d1⟩ := pinAt_run (x := ConLeche.natAddName) hp rfl q1
  rw [p1] at w1
  obtain ⟨hsu, u2, q2, w2⟩ := AM.bind_ok w1
  obtain ⟨p2, d2⟩ := pinAt_run (x := ConLeche.natSubName) hp rfl q2
  rw [p2] at w2
  obtain ⟨hmu, u3, q3, w3⟩ := AM.bind_ok w2
  obtain ⟨p3, d3⟩ := pinAt_run (x := ConLeche.natMulName) hp rfl q3
  rw [p3] at w3
  obtain ⟨hpo, u4, q4, w4⟩ := AM.bind_ok w3
  obtain ⟨p4, d4⟩ := pinAt_run (x := ConLeche.natPowName) hp rfl q4
  rw [p4] at w4
  obtain ⟨hbe, u5, q5, w5⟩ := AM.bind_ok w4
  obtain ⟨p5, d5⟩ := pinAt_run (x := ConLeche.natBeqName) hp rfl q5
  rw [p5] at w5
  obtain ⟨hbl, u6, q6, w6⟩ := AM.bind_ok w5
  obtain ⟨p6, d6⟩ := pinAt_run (x := ConLeche.natBleName) hp rfl q6
  rw [p6] at w6
  obtain ⟨hdi, u7, q7, w7⟩ := AM.bind_ok w6
  obtain ⟨p7, d7⟩ := pinAt_run (x := ConLeche.natDivName) hp rfl q7
  rw [p7] at w7
  obtain ⟨hmo, u8, q8, w8⟩ := AM.bind_ok w7
  obtain ⟨p8, d8⟩ := pinAt_run (x := ConLeche.natModName) hp rfl q8
  rw [p8] at w8
  obtain ⟨hgc, u9, q9, w9⟩ := AM.bind_ok w8
  obtain ⟨p9, d9⟩ := pinAt_run (x := ConLeche.natGcdName) hp rfl q9
  rw [p9] at w9
  obtain ⟨hla, u10, q10, w10⟩ := AM.bind_ok w9
  obtain ⟨p10, d10⟩ := pinAt_run (x := ConLeche.natLandName) hp rfl q10
  rw [p10] at w10
  obtain ⟨hlo, u11, q11, w11⟩ := AM.bind_ok w10
  obtain ⟨p11, d11⟩ := pinAt_run (x := ConLeche.natLorName) hp rfl q11
  rw [p11] at w11
  obtain ⟨hxo, u12, q12, w12⟩ := AM.bind_ok w11
  obtain ⟨p12, d12⟩ := pinAt_run (x := ConLeche.natXorName) hp rfl q12
  rw [p12] at w12
  obtain ⟨hsl, u13, q13, w13⟩ := AM.bind_ok w12
  obtain ⟨p13, d13⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp rfl q13
  rw [p13] at w13
  obtain ⟨hsr, u14, q14, w14⟩ := AM.bind_ok w13
  obtain ⟨p14, d14⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp rfl q14
  rw [p14] at w14
  -- the frame every arm shares
  have frame : ∀ out : List NIdx, (pure out : AM (List NIdx)) s = .ok (ds, s') →
      denoteNL s.store out (ConLeche.natOpDeps nm) →
      StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
        s'.pins = s.pins ∧ denoteNL s'.store ds (ConLeche.natOpDeps nm) := by
    intro out hpure hd
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hpure
    exact ⟨hok, Ext.refl _, rfl, rfl, hd⟩
  -- a handle test IS a name test
  have b0 : (cn == hpr) = true ↔ nm = ConLeche.natPredName := beq_handle_iff hok.wf hn d0
  have b1 : (cn == had) = true ↔ nm = ConLeche.natAddName := beq_handle_iff hok.wf hn d1
  have b2 : (cn == hsu) = true ↔ nm = ConLeche.natSubName := beq_handle_iff hok.wf hn d2
  have b3 : (cn == hmu) = true ↔ nm = ConLeche.natMulName := beq_handle_iff hok.wf hn d3
  have b4 : (cn == hpo) = true ↔ nm = ConLeche.natPowName := beq_handle_iff hok.wf hn d4
  have b5 : (cn == hbe) = true ↔ nm = ConLeche.natBeqName := beq_handle_iff hok.wf hn d5
  have b6 : (cn == hbl) = true ↔ nm = ConLeche.natBleName := beq_handle_iff hok.wf hn d6
  have b7 : (cn == hdi) = true ↔ nm = ConLeche.natDivName := beq_handle_iff hok.wf hn d7
  have b8 : (cn == hmo) = true ↔ nm = ConLeche.natModName := beq_handle_iff hok.wf hn d8
  have b9 : (cn == hgc) = true ↔ nm = ConLeche.natGcdName := beq_handle_iff hok.wf hn d9
  have b10 : (cn == hla) = true ↔ nm = ConLeche.natLandName := beq_handle_iff hok.wf hn d10
  have b11 : (cn == hlo) = true ↔ nm = ConLeche.natLorName := beq_handle_iff hok.wf hn d11
  have b12 : (cn == hxo) = true ↔ nm = ConLeche.natXorName := beq_handle_iff hok.wf hn d12
  have b13 : (cn == hsl) = true ↔ nm = ConLeche.natShiftLeftName := beq_handle_iff hok.wf hn d13
  have b14 : (cn == hsr) = true ↔ nm = ConLeche.natShiftRightName := beq_handle_iff hok.wf hn d14
  -- the sixteen arms
  rcases AM.ite_ok w14 with ⟨y0, a0⟩ | ⟨z0, v0⟩
  · exact frame _ a0 (by simp only [ConLeche.natOpDeps, if_pos (b0.mp y0)]; exact ⟨d0, trivial⟩)
  have nb0 : ¬ (nm = ConLeche.natPredName) := fun h => z0 (b0.mpr h)
  rcases AM.ite_ok v0 with ⟨y1, a1⟩ | ⟨z1, v1⟩
  · exact frame _ a1 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_pos (b1.mp y1)]; exact ⟨d1, trivial⟩)
  have nb1 : ¬ (nm = ConLeche.natAddName) := fun h => z1 (b1.mpr h)
  rcases AM.ite_ok v1 with ⟨y2, a2⟩ | ⟨z2, v2⟩
  · exact frame _ a2 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_pos (b2.mp y2)]; exact ⟨d0, d2, trivial⟩)
  have nb2 : ¬ (nm = ConLeche.natSubName) := fun h => z2 (b2.mpr h)
  rcases AM.ite_ok v2 with ⟨y3, a3⟩ | ⟨z3, v3⟩
  · exact frame _ a3 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_pos (b3.mp y3)]; exact ⟨d1, d3, trivial⟩)
  have nb3 : ¬ (nm = ConLeche.natMulName) := fun h => z3 (b3.mpr h)
  rcases AM.ite_ok v3 with ⟨y4, a4⟩ | ⟨z4, v4⟩
  · exact frame _ a4 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_pos (b4.mp y4)]; exact ⟨d1, d3, d4, trivial⟩)
  have nb4 : ¬ (nm = ConLeche.natPowName) := fun h => z4 (b4.mpr h)
  rcases AM.ite_ok v4 with ⟨y5, a5⟩ | ⟨z5, v5⟩
  · exact frame _ a5 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_pos (b5.mp y5)]; exact ⟨d5, trivial⟩)
  have nb5 : ¬ (nm = ConLeche.natBeqName) := fun h => z5 (b5.mpr h)
  rcases AM.ite_ok v5 with ⟨y6, a6⟩ | ⟨z6, v6⟩
  · exact frame _ a6 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_pos (b6.mp y6)]; exact ⟨d6, trivial⟩)
  have nb6 : ¬ (nm = ConLeche.natBleName) := fun h => z6 (b6.mpr h)
  rcases AM.ite_ok v6 with ⟨y7, a7⟩ | ⟨z7, v7⟩
  · exact frame _ a7 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_pos (b7.mp y7)]; exact ⟨d0, d2, d6, d7, trivial⟩)
  have nb7 : ¬ (nm = ConLeche.natDivName) := fun h => z7 (b7.mpr h)
  rcases AM.ite_ok v7 with ⟨y8, a8⟩ | ⟨z8, v8⟩
  · exact frame _ a8 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_pos (b8.mp y8)]; exact ⟨d0, d2, d6, d8, trivial⟩)
  have nb8 : ¬ (nm = ConLeche.natModName) := fun h => z8 (b8.mpr h)
  rcases AM.ite_ok v8 with ⟨y9, a9⟩ | ⟨z9, v9⟩
  · exact frame _ a9 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_pos (b9.mp y9)]; exact ⟨d6, d8, d9, trivial⟩)
  have nb9 : ¬ (nm = ConLeche.natGcdName) := fun h => z9 (b9.mpr h)
  rcases AM.ite_ok v9 with ⟨y10, a10⟩ | ⟨z10, v10⟩
  · exact frame _ a10 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_pos (b10.mp y10)]; exact ⟨d1, d3, d6, d7, d8, d10, trivial⟩)
  have nb10 : ¬ (nm = ConLeche.natLandName) := fun h => z10 (b10.mpr h)
  rcases AM.ite_ok v10 with ⟨y11, a11⟩ | ⟨z11, v11⟩
  · exact frame _ a11 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_pos (b11.mp y11)]; exact ⟨d1, d2, d3, d6, d7, d8, d11, trivial⟩)
  have nb11 : ¬ (nm = ConLeche.natLorName) := fun h => z11 (b11.mpr h)
  rcases AM.ite_ok v11 with ⟨y12, a12⟩ | ⟨z12, v12⟩
  · exact frame _ a12 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_pos (b12.mp y12)]; exact ⟨d1, d3, d6, d7, d8, d12, trivial⟩)
  have nb12 : ¬ (nm = ConLeche.natXorName) := fun h => z12 (b12.mpr h)
  rcases AM.ite_ok v12 with ⟨y13, a13⟩ | ⟨z13, v13⟩
  · exact frame _ a13 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_neg nb12, if_pos (b13.mp y13)]; exact ⟨d2, d3, d6, d13, trivial⟩)
  have nb13 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z13 (b13.mpr h)
  rcases AM.ite_ok v13 with ⟨y14, a14⟩ | ⟨z14, v14⟩
  · exact frame _ a14 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_neg nb12, if_neg nb13, if_pos (b14.mp y14)]; exact ⟨d2, d6, d7, d14, trivial⟩)
  have nb14 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z14 (b14.mpr h)
  exact frame _ v14 (by simp only [ConLeche.natOpDeps, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6, if_neg nb7, if_neg nb8, if_neg nb9, if_neg nb10, if_neg nb11, if_neg nb12, if_neg nb13, if_neg nb14]; exact trivial)

/-! ## The structural-`Nat` guard, link by link

`natOpGuard` and `natOpStoredOk` read pins, build `constE`s and compare
HANDLES; none of them interns a whole `ConstantInfo`.  They are read through
`Bridge/Checker/Basis.lean`'s `RunsB` combinators, with four local helpers:
`constE_run`, the handle comparison at expressions (`beqE_of_denote`), the
level-parameter emptiness transfer (`lpsEmpty_of_denote`), and — for the
two `Bool` constructor lookups — `toConstantVal_sstep` at a stored constant,
whose `.projInfo` premise `IFEnvOK.proj` discharges. -/

/-- con-leche: none — `constE n` is `.const n []`, interned. -/
theorem constE_run {n : NIdx} {nm : ConLeche.Name} {e : EIdx} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hr : constE n s = .ok (e, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store e = some (.const nm []) := by
  simp only [Arena.constE] at hr
  obtain ⟨us, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨rfl, hus⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteLs s.store.lss r = some []) rfl g1
    (pinEmptyLevels_spec s hp)
  obtain ⟨ls, hv, -⟩ := denoteLs_view hus
  obtain ⟨hs, hd⟩ := Frontend.internE_sstep hst
    (viewOK_const (nview_isSome_of_denote hn) (by rw [hv]; rfl)) r1
  refine ⟨hs, ?_⟩
  rw [hd]
  simp only [denoteEView, denoteN_ext hn hs.ext, denoteLs_ext hus hs.ext, opt2]

/-- con-leche: none — `sortOne` reads the pinned `Sort 1`. -/
theorem sortOne_run {e : EIdx} {s s' : AState} (hp : PinsOK s)
    (hr : sortOne s = .ok (e, s')) :
    s' = s ∧ denoteE s.store e = some (.sort (.succ .zero)) :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteE s.store r = some (.sort (.succ .zero)))
    rfl hr (pinSortOne_spec s hp)

/-- con-leche: none — a handle comparison at expressions IS the comparison of
the two denotations (`denoteE_inj`). -/
theorem beqE_of_denote {st : EStore} (hwf : StoreWF st) {a b : EIdx}
    {x y : Expr} (ha : denoteE st a = some x) (hb : denoteE st b = some y) :
    (a == b) = (x == y) :=
  beq_of_denote_inj (fun h1 h2 => denoteE_inj hwf h1 h2) ha hb

/-- con-leche: none — a stored constant's level parameters are empty iff its
denotation's are (`denoteNList` preserves length). -/
theorem lpsEmpty_of_denote {st : EStore} {v : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st v = some c) :
    v.levelParams.isEmpty = c.levelParams.isEmpty := by
  have hl := denoteNList_length _ _ (denoteCV_inv h).2.1
  cases h1 : v.levelParams <;> cases h2 : c.levelParams <;> simp_all

/-- con-leche: none — the frame at a caller that reads the index at a stored
constant: `IFEnvOK.proj` makes every stored table rightly named. -/
theorem CIProjNamed_of_find {env : Env} {fe : IFEnv} {s : AState}
    (hie : IFEnvOK env fe s) {n : NIdx} {ci : IConstantInfo}
    (hf : fe.find? n = some ci) : Frontend.CIProjNamed s.store ci := by
  intro t ht
  subst ht
  exact (hie.proj n t hf).toNamed

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:202-206 natIndOk -/
theorem natIndOk_run {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hxy : FindRel s.store x y) :
    RunsB (Arena.natIndOk x) s (ConLeche.natIndOk y) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hst
  · cases ci
    case indInfo v cap =>
      obtain ⟨v', d, rfl, hv, -⟩ := denoteCI_ind_inv hd
      simp only [Arena.natIndOk, ConLeche.natIndOk]
      refine RunsB.bind fun {e s1} g1 => ?_
      obtain ⟨rfl, he⟩ := sortOne_run hp g1
      refine ⟨Frontend.IStepS.refl hst, ?_⟩
      rw [lpsEmpty_of_denote hv, beqE_of_denote hst.wf (denoteCV_inv hv).2.2 he]
      exact RunsB.ret hst
    all_goals first
      | (obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, rfl, _⟩ := denoteCI_ctor_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_defn_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_thm_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_rec_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, rfl, _⟩ := denoteCI_proj_inv hd; exact RunsB.ret hst)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk -/
theorem natZeroOk_run {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hxy : FindRel s.store x y) :
    RunsB (Arena.natZeroOk x) s (ConLeche.natZeroOk y) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hst
  · cases ci
    case ctorInfo v nP nF =>
      obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      simp only [Arena.natZeroOk, ConLeche.natZeroOk]
      refine RunsB.pin hst hp (x := ConLeche.natName) (by rfl) fun nt dnt => ?_
      refine RunsB.bind fun {e s1} g1 => ?_
      obtain ⟨hs1, he⟩ := constE_run hst hp dnt g1
      refine ⟨hs1, ?_⟩
      rw [lpsEmpty_of_denote hv, beqE_of_denote hs1.ok.wf
        (denoteCV_inv (denoteCV_ext hv hs1.ext)).2.2 he]
      exact RunsB.ret hs1.ok
    all_goals first
      | (obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_ind_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_defn_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_thm_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_rec_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, rfl, _⟩ := denoteCI_proj_inv hd; exact RunsB.ret hst)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — the pinned
type test `.forallE (.const natName []) (.const natName []) _`, restated as
two expression comparisons: that is what the arena's two handle comparisons
against the interned `constE` decide. -/
def natSuccTy : Expr → Bool
  | .forallE dom body _ =>
    dom == .const ConLeche.natName [] && body == .const ConLeche.natName []
  | _ => false

theorem natSuccOk_eq (cv : ConstantVal) (nP nF : Nat) :
    ConLeche.natSuccOk (some (.ctorInfo cv nP nF)) =
      (cv.levelParams.isEmpty && natSuccTy cv.type) := by
  simp only [ConLeche.natSuccOk]
  congr 1
  cases ht : cv.type with
  | forallE dx bx m =>
    simp only [natSuccTy]
    cases dx <;> cases bx <;> (try simp)
    all_goals
      rename_i n1 ls1 n2 ls2
      cases ls1 <;> cases ls2 <;> (try simp)
      rw [Bool.eq_iff_iff]
      simp [beq_iff_eq]
  | _ => rfl

theorem natSuccOk_run {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hxy : FindRel s.store x y) :
    RunsB (Arena.natSuccOk x) s (ConLeche.natSuccOk y) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hst
  · cases ci
    case ctorInfo v nP nF =>
      obtain ⟨v', rfl, hv⟩ := denoteCI_ctor_inv hd
      rw [natSuccOk_eq]
      simp only [Arena.natSuccOk]
      refine RunsB.guard hst (by rw [lpsEmpty_of_denote hv]) fun _ => ?_
      refine RunsB.pin hst hp (x := ConLeche.natName) (by rfl) fun nt dnt => ?_
      refine RunsB.bind fun {e s1} g1 => ?_
      obtain ⟨hs1, he⟩ := constE_run hst hp dnt g1
      refine ⟨hs1, RunsB.bind fun {vw s2} g2 => ?_⟩
      obtain ⟨rfl, hvw⟩ := viewE_run g2
      refine ⟨Frontend.IStepS.refl hs1.ok, ?_⟩
      have hty := (denoteCV_inv (denoteCV_ext hv hs1.ext)).2.2
      have hwf := hs1.ok.wf
      cases vw
      case forallE dom body mb =>
        obtain ⟨dx, bx, hx, hdx, hbx⟩ := denote_forallE_inv hwf hvw hty
        rw [hx]
        show RunsB _ _ (dx == _ && bx == _)
        rw [← beqE_of_denote hwf hdx he, ← beqE_of_denote hwf hbx he]
        exact RunsB.ret hs1.ok
      all_goals first
        | (have hx := denote_bvar_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (obtain ⟨_, hx, _⟩ := denote_fvar_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (obtain ⟨_, hx, _⟩ := denote_sort_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (obtain ⟨_, _, hx, _⟩ := denote_const_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (obtain ⟨_, _, hx, _⟩ := denote_app_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (obtain ⟨_, _, hx, _⟩ := denote_lam_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (obtain ⟨_, _, _, hx, _⟩ := denote_letE_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (have hx := denote_lit_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
        | (obtain ⟨_, _, hx, _⟩ := denote_proj_inv hwf hvw hty; rw [hx]; exact RunsB.ret hs1.ok)
    all_goals first
      | (obtain ⟨_, rfl, _⟩ := denoteCI_axiom_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_ind_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_defn_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_thm_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, _, rfl, _⟩ := denoteCI_rec_inv hd; exact RunsB.ret hst)
      | (obtain ⟨_, rfl, _⟩ := denoteCI_proj_inv hd; exact RunsB.ret hst)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:225-233 natLitSupported -/
theorem natLitSupported_run {env : Env} {fe : IFEnv} {s : AState}
    (hst : StateOK s) (hp : PinsOK s) (hie : IFEnvOK env fe s) :
    RunsB (Arena.natLitSupported fe) s (ConLeche.natLitSupported env) := by
  simp only [ConLeche.natLitSupported, Bool.and_assoc]
  unfold Arena.natLitSupported
  refine RunsB.pin hst hp (x := ConLeche.natName) (by rfl) fun n1 d1 => ?_
  refine RunsB.bindB (natIndOk_run hst hp (hie.findRel hst d1)) fun {s1} hs1 => ?_
  have hp1 := hp.mono hs1.ext hs1.pins
  have hie1 := hie.mono hs1.ext
  refine RunsB.guard hs1.ok (by simp) fun _ => ?_
  refine RunsB.pin hs1.ok hp1 (x := ConLeche.natZeroName) (by rfl) fun n2 d2 => ?_
  refine RunsB.bindB (natZeroOk_run hs1.ok hp1 (hie1.findRel hs1.ok d2))
    fun {s2} hs2 => ?_
  have hp2 := hp1.mono hs2.ext hs2.pins
  have hie2 := hie1.mono hs2.ext
  refine RunsB.guard hs2.ok (by simp) fun _ => ?_
  refine RunsB.pin hs2.ok hp2 (x := ConLeche.natSuccName) (by rfl) fun n3 d3 => ?_
  exact natSuccOk_run hs2.ok hp2 (hie2.findRel hs2.ok d3)

/-- con-leche: none — `natOpDeps` reads fifteen pins and returns a literal
list; it leaves the state alone (`natOpDeps_run` carries the frame as four
clauses, this is the equation the `RunsB` chain needs). -/
theorem natOpDeps_state {cn : NIdx} {ds : List NIdx} {s s' : AState}
    (hp : PinsOK s) (hr : natOpDeps cn s = .ok (ds, s')) : s' = s := by
  simp only [Arena.natOpDeps] at hr
  obtain ⟨_, u0, q0, w0⟩ := AM.bind_ok hr
  obtain ⟨p0, -⟩ := pinAt_run (x := ConLeche.natPredName) hp rfl q0
  rw [p0] at w0
  obtain ⟨_, u1, q1, w1⟩ := AM.bind_ok w0
  obtain ⟨p1, -⟩ := pinAt_run (x := ConLeche.natAddName) hp rfl q1
  rw [p1] at w1
  obtain ⟨_, u2, q2, w2⟩ := AM.bind_ok w1
  obtain ⟨p2, -⟩ := pinAt_run (x := ConLeche.natSubName) hp rfl q2
  rw [p2] at w2
  obtain ⟨_, u3, q3, w3⟩ := AM.bind_ok w2
  obtain ⟨p3, -⟩ := pinAt_run (x := ConLeche.natMulName) hp rfl q3
  rw [p3] at w3
  obtain ⟨_, u4, q4, w4⟩ := AM.bind_ok w3
  obtain ⟨p4, -⟩ := pinAt_run (x := ConLeche.natPowName) hp rfl q4
  rw [p4] at w4
  obtain ⟨_, u5, q5, w5⟩ := AM.bind_ok w4
  obtain ⟨p5, -⟩ := pinAt_run (x := ConLeche.natBeqName) hp rfl q5
  rw [p5] at w5
  obtain ⟨_, u6, q6, w6⟩ := AM.bind_ok w5
  obtain ⟨p6, -⟩ := pinAt_run (x := ConLeche.natBleName) hp rfl q6
  rw [p6] at w6
  obtain ⟨_, u7, q7, w7⟩ := AM.bind_ok w6
  obtain ⟨p7, -⟩ := pinAt_run (x := ConLeche.natDivName) hp rfl q7
  rw [p7] at w7
  obtain ⟨_, u8, q8, w8⟩ := AM.bind_ok w7
  obtain ⟨p8, -⟩ := pinAt_run (x := ConLeche.natModName) hp rfl q8
  rw [p8] at w8
  obtain ⟨_, u9, q9, w9⟩ := AM.bind_ok w8
  obtain ⟨p9, -⟩ := pinAt_run (x := ConLeche.natGcdName) hp rfl q9
  rw [p9] at w9
  obtain ⟨_, u10, q10, w10⟩ := AM.bind_ok w9
  obtain ⟨p10, -⟩ := pinAt_run (x := ConLeche.natLandName) hp rfl q10
  rw [p10] at w10
  obtain ⟨_, u11, q11, w11⟩ := AM.bind_ok w10
  obtain ⟨p11, -⟩ := pinAt_run (x := ConLeche.natLorName) hp rfl q11
  rw [p11] at w11
  obtain ⟨_, u12, q12, w12⟩ := AM.bind_ok w11
  obtain ⟨p12, -⟩ := pinAt_run (x := ConLeche.natXorName) hp rfl q12
  rw [p12] at w12
  obtain ⟨_, u13, q13, w13⟩ := AM.bind_ok w12
  obtain ⟨p13, -⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp rfl q13
  rw [p13] at w13
  obtain ⟨_, u14, q14, w14⟩ := AM.bind_ok w13
  obtain ⟨p14, -⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp rfl q14
  rw [p14] at w14
  clear hr
  repeat' first
    | (obtain ⟨-, rfl⟩ := AM.pure_ok w14; rfl)
    | (rcases AM.ite_ok w14 with ⟨-, w14⟩ | ⟨-, w14⟩)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard — the
dependency half: `natOpDepsStored` is con-leche's `(natOpDeps c).all …`. -/
theorem natOpDepsStored_run {env : Env} {fe : IFEnv} :
    ∀ (ds : List NIdx) (xs : List ConLeche.Name) {s : AState}, StateOK s →
      IFEnvOK env fe s → denoteNL s.store ds xs →
      RunsB (Arena.natOpDepsStored fe ds) s
        (xs.all fun n => match env.find? n with
          | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
          | _ => false) := by
  intro ds
  induction ds with
  | nil =>
    intro xs s hst _ hd
    cases xs with
    | nil => exact RunsB.ret hst
    | cons x xs => exact absurd hd (by simp [denoteNL])
  | cons d ds ih =>
    intro xs s hst hie hd
    cases xs with
    | nil => exact absurd hd (by simp [denoteNL])
    | cons x xs =>
      obtain ⟨hd1, hdt⟩ := hd
      rw [List.all_cons]
      simp only [Arena.natOpDepsStored]
      refine RunsB.matchDefn hst (hie.findRel hst hd1) fun v v' hv => ?_
      exact RunsB.guardT hst (lpsEmpty_of_denote hv) fun _ => ih xs hst hie hdt

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpGuard) — the
structural-`Nat` environment guard is con-leche's at the denoted environment.

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4 — the same
defect as `natOpDeps_run`'s above, found by the grep that round asks for):
`natOpGuard` reads eight pins (`natLitSupported`'s three, `natBeqName`,
`natBleName`, `natDivModNames`, `boolTrueName`, `boolFalseName`) and asked
only for `StateOK`, so nothing made the handles `pinAt` hands back denote
anything and the conclusion was not provable.  Free at the one call site
(`Bridge/Checker/Arms.lean`'s `defn` arm, `hok4.check.pins`).

**PROVED** (task #97-P3-Checker round 8): the `do`-block read link by link
through `Basis.lean`'s `RunsB` combinators — `natLitSupported_run`,
`natOpDeps_run` / `natOpDeps_state`, `natOpDepsStored_run`, and the two `Bool`
constructor lookups through `RunsB.matchLps` (whose `.projInfo` premise
`IFEnvOK.proj` discharges).  Round 10 moved the chain into
`natOpGuard_runsB` (below), which `divModEnvGuard` binds. -/
theorem natOpGuard_runsB {env2 : Env} {fe2 : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {s : AState} (hok : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns cn = some nm) :
    RunsB (natOpGuard fe2 cn) s (ConLeche.natOpGuard env2 nm) := by
  simp only [ConLeche.natOpGuard, Bool.and_assoc]
  unfold Arena.natOpGuard
  refine RunsB.bindB (natLitSupported_run hok hp hie) fun {s1} hs1 => ?_
  have hp1 := hp.mono hs1.ext hs1.pins
  have hie1 := hie.mono hs1.ext
  have hn1 := denoteN_ext hn hs1.ext
  refine RunsB.guard hs1.ok (by simp) fun _ => ?_
  refine RunsB.bind fun {ds s2} g2 => ?_
  obtain rfl := natOpDeps_state hp1 g2
  obtain ⟨-, -, -, -, hds⟩ := natOpDeps_run hs1.ok hp1 hn1 g2
  refine ⟨Frontend.IStepS.refl hs1.ok, ?_⟩
  refine RunsB.bindB (natOpDepsStored_run ds _ hs1.ok hie1 hds)
    fun {s3} hs3 => ?_
  have hp3 := hp1.mono hs3.ext hs3.pins
  have hie3 := hie1.mono hs3.ext
  have hn3 := denoteN_ext hn1 hs3.ext
  have st3 := hs3.ok
  refine RunsB.guard st3 (by first | rfl | simp) fun _ => ?_
  refine RunsB.pin st3 hp3 (x := ConLeche.natBeqName) (by rfl) fun be dbe => ?_
  refine RunsB.pin st3 hp3 (x := ConLeche.natBleName) (by rfl) fun bl dbl => ?_
  refine RunsB.bind fun {dm s4} g4 => ?_
  obtain ⟨rfl, hdm⟩ := natDivModNames_run hp3 g4
  refine ⟨Frontend.IStepS.refl st3, ?_⟩
  have e1 := beq_handle_iff st3.wf hn3 dbe
  have e2 := beq_handle_iff st3.wf hn3 dbl
  have e3 : dm.contains cn = ConLeche.natDivModNames.contains nm :=
    denoteNList_contains st3.wf dm _ (denoteNL_toList _ _ hdm) cn nm hn3
  refine RunsB.ite (by simp only [Bool.or_eq_true, e1, e2, e3, decide_eq_true_eq])
    (fun _ => ?_) (fun _ => RunsB.ret st3)
  refine RunsB.pin st3 hp3 (x := ConLeche.boolTrueName) (by rfl) fun bt dbt => ?_
  refine RunsB.matchLpsJP st3 (hie3.findRel st3 dbt)
    (fun ci hf => CIProjNamed_of_find hie3 hf) fun {s5} hs5 => ?_
  have hp5 := hp3.mono hs5.ext hs5.pins
  have hie5 := hie3.mono hs5.ext
  refine RunsB.guard hs5.ok (by first | rfl | simp) fun _ => ?_
  refine RunsB.pin hs5.ok hp5 (x := ConLeche.boolFalseName) (by rfl) fun bf dbf => ?_
  exact RunsB.matchLps hs5.ok (hie5.findRel hs5.ok dbf)
    fun ci hf => CIProjNamed_of_find hie5 hf

theorem natOpGuard_run {env2 : Env} {fe2 : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpGuard fe2 cn s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.natOpGuard env2 nm := by
  obtain ⟨hs, rfl⟩ := natOpGuard_runsB hok hp hie hn _ _ hr
  exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:640-650 natOpCod -/
theorem natOpCod_run {env : Env} {fe : IFEnv} {cH : NIdx} {cn : ConLeche.Name}
    {e : EIdx} {x : Expr} {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env fe s) (hc : denoteN s.store.ns cH = some cn)
    (he : denoteE s.store e = some x) :
    RunsB (Arena.natOpCod fe cH e) s (ConLeche.natOpCod env cn x) := by
  unfold Arena.natOpCod ConLeche.natOpCod
  refine RunsB.pin hst hp (x := ConLeche.natBeqName) (by rfl) fun be dbe => ?_
  refine RunsB.pin hst hp (x := ConLeche.natBleName) (by rfl) fun bl dbl => ?_
  have e1 := beq_handle_iff hst.wf hc dbe
  have e2 := beq_handle_iff hst.wf hc dbl
  refine RunsB.ite (by simp only [Bool.or_eq_true, e1, e2, decide_eq_true_eq])
    (fun _ => ?_) (fun _ => ?_)
  · refine RunsB.pin hst hp (x := ConLeche.boolName) (by rfl) fun bn dbn => ?_
    refine RunsB.bind fun {bc s1} g1 => ?_
    obtain ⟨hs1, hbc⟩ := constE_run hst hp dbn g1
    refine ⟨hs1, ?_⟩
    refine RunsB.guard hs1.ok (by
      simp only [bne, beqE_of_denote hs1.ok.wf (denote_ext he hs1.ext) hbc]) fun _ => ?_
    exact RunsB.matchCod hs1.ok (hp.mono hs1.ext hs1.pins)
      ((hie.mono hs1.ext).findRel hs1.ok (denoteN_ext dbn hs1.ext))
      fun ci hf => CIProjNamed_of_find (hie.mono hs1.ext) hf
  · refine RunsB.pin hst hp (x := ConLeche.natName) (by rfl) fun nn dnn => ?_
    refine RunsB.bind fun {nc s1} g1 => ?_
    obtain ⟨hs1, hnc⟩ := constE_run hst hp dnn g1
    refine ⟨hs1, ?_⟩
    rw [← beqE_of_denote hs1.ok.wf (denote_ext he hs1.ext) hnc]
    exact RunsB.ret hs1.ok

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:652-667 natOpTyPinned -/
theorem natOpTyPinned_run {env : Env} {fe : IFEnv} {cH : NIdx}
    {cn : ConLeche.Name} {ty : EIdx} {x : Expr} {s : AState} (hst : StateOK s)
    (hp : PinsOK s) (hie : IFEnvOK env fe s)
    (hc : denoteN s.store.ns cH = some cn)
    (hty : denoteE s.store ty = some x) :
    RunsB (Arena.natOpTyPinned fe cH ty) s (ConLeche.natOpTyPinned env cn x) := by
  unfold Arena.natOpTyPinned ConLeche.natOpTyPinned
  refine RunsB.pin hst hp (x := ConLeche.natName) (by rfl) fun nn dnn => ?_
  refine RunsB.bind fun {nc s1} g1 => ?_
  obtain ⟨hs1, hnc⟩ := constE_run hst hp dnn g1
  refine ⟨hs1, ?_⟩
  have st1 := hs1.ok
  have hwf := st1.wf
  have hp1 := hp.mono hs1.ext hs1.pins
  have hie1 := hie.mono hs1.ext
  have hc1 := denoteN_ext hc hs1.ext
  have hty1 := denote_ext hty hs1.ext
  refine RunsB.pin st1 hp1 (x := ConLeche.natPredName) (by rfl) fun pr dpr => ?_
  refine RunsB.ite (beq_handle_iff hwf hc1 dpr) (fun _ => ?_) (fun _ => ?_)
  · refine RunsB.bind fun {vw s2} g2 => ?_
    obtain ⟨rfl, hvw⟩ := viewE_run g2
    refine ⟨Frontend.IStepS.refl st1, ?_⟩
    cases vw
    case forallE dom body mb =>
      obtain ⟨dx, bx, rfl, hdx, hbx⟩ := denote_forallE_inv hwf hvw hty1
      exact RunsB.guardT st1 (beqE_of_denote hwf hdx hnc)
        fun _ => natOpCod_run st1 hp1 hie1 hc1 hbx
    all_goals first
      | (obtain rfl := denote_bvar_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, rfl, _⟩ := denote_fvar_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, rfl, _⟩ := denote_sort_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_const_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_app_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_lam_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, _, rfl, _⟩ := denote_letE_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain rfl := denote_lit_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_proj_inv hwf hvw hty1; exact RunsB.ret st1)
  · refine RunsB.bind fun {vw s2} g2 => ?_
    obtain ⟨rfl, hvw⟩ := viewE_run g2
    refine ⟨Frontend.IStepS.refl st1, ?_⟩
    cases vw
    case forallE dom rest mb =>
      obtain ⟨dx, rx, rfl, hdx, hrx⟩ := denote_forallE_inv hwf hvw hty1
      refine RunsB.bind fun {vr s3} g3 => ?_
      obtain ⟨rfl, hvr⟩ := viewE_run g3
      refine ⟨Frontend.IStepS.refl st1, ?_⟩
      cases vr
      case forallE dom2 body mb2 =>
        obtain ⟨dx2, bx, rfl, hdx2, hbx⟩ := denote_forallE_inv hwf hvr hrx
        refine RunsB.guardT st1 ?_ fun _ => natOpCod_run st1 hp1 hie1 hc1 hbx
        rw [beqE_of_denote hwf hdx hnc, beqE_of_denote hwf hdx2 hnc]
      all_goals first
        | (obtain rfl := denote_bvar_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain ⟨_, rfl, _⟩ := denote_fvar_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain ⟨_, rfl, _⟩ := denote_sort_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain ⟨_, _, rfl, _⟩ := denote_const_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain ⟨_, _, rfl, _⟩ := denote_app_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain ⟨_, _, rfl, _⟩ := denote_lam_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain ⟨_, _, _, rfl, _⟩ := denote_letE_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain rfl := denote_lit_inv hwf hvr hrx; exact RunsB.ret st1)
        | (obtain ⟨_, _, rfl, _⟩ := denote_proj_inv hwf hvr hrx; exact RunsB.ret st1)
    all_goals first
      | (obtain rfl := denote_bvar_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, rfl, _⟩ := denote_fvar_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, rfl, _⟩ := denote_sort_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_const_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_app_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_lam_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, _, rfl, _⟩ := denote_letE_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain rfl := denote_lit_inv hwf hvw hty1; exact RunsB.ret st1)
      | (obtain ⟨_, _, rfl, _⟩ := denote_proj_inv hwf hvw hty1; exact RunsB.ret st1)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:669-675 natOpStoredOk -/
theorem natOpStoredOk_run {env : Env} {fe : IFEnv} {cH : NIdx}
    {cn : ConLeche.Name} {s : AState} (hst : StateOK s) (hp : PinsOK s)
    (hie : IFEnvOK env fe s) (hc : denoteN s.store.ns cH = some cn) :
    RunsB (Arena.natOpStoredOk fe cH) s (ConLeche.natOpStoredOk env cn) := by
  unfold Arena.natOpStoredOk ConLeche.natOpStoredOk
  refine RunsB.and_true
    (RunsB.matchDefn hst (hie.findRel hst hc) fun v v' hv => ?_)
  rw [Bool.and_true]
  exact RunsB.guardT hst (lpsEmpty_of_denote hv) fun _ =>
    natOpTyPinned_run hst hp hie hc (denoteCV_inv hv).2.2

theorem natOpStoredOkAll_runs {env : Env} {fe : IFEnv} :
    ∀ (ds : List NIdx) (xs : List ConLeche.Name) {s : AState}, StateOK s →
      PinsOK s → IFEnvOK env fe s → denoteNL s.store ds xs →
      RunsB (Arena.natOpStoredOkAll fe ds) s
        (xs.all (ConLeche.natOpStoredOk env)) := by
  intro ds
  induction ds with
  | nil =>
    intro xs s hst _ _ hd
    cases xs with
    | nil => exact RunsB.ret hst
    | cons x xs => exact absurd hd (by simp [denoteNL])
  | cons d ds ih =>
    intro xs s hst hp hie hd
    cases xs with
    | nil => exact absurd hd (by simp [denoteNL])
    | cons x xs =>
      obtain ⟨hd1, hdt⟩ := hd
      rw [List.all_cons]
      simp only [Arena.natOpStoredOkAll]
      refine RunsB.bindB (natOpStoredOk_run hst hp hie hd1) fun {s1} hs1 => ?_
      exact RunsB.guardT hs1.ok rfl fun _ =>
        ih xs hs1.ok (hp.mono hs1.ext hs1.pins) (hie.mono hs1.ext)
          (denoteNL_ext hs1.ext _ _ hdt)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpStoredOk) — the twin's list
recursion answers con-leche's `List.all` (DESIGN §3.4 forbids the closure).

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4): each step
is `natOpStoredOk`, which is `natOpTyPinned` on a hit, which reads the pin
table — so this walk is a pin reader too and `StateOK` alone was not enough.
Free at the one call site (`hok5.check.pins`).

**PROVED** (task #97-P3-Checker round 8): `natOpStoredOkAll_runs`, a list
induction over `natOpStoredOk_run` (`natOpTyPinned_run`, `natOpCod_run`). -/
theorem natOpStoredOkAll_run {env2 : Env} {fe2 : IFEnv} {ds : List NIdx}
    {xs : List ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hd : denoteNL s.store ds xs)
    (hr : natOpStoredOkAll fe2 ds s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = xs.all (ConLeche.natOpStoredOk env2) := by
  obtain ⟨hs, rfl⟩ := natOpStoredOkAll_runs ds xs hok hp hie hd _ _ hr
  exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩

/-- con-leche: none — an interned `fvar` node denotes the `fvar` at its type's
denotation. -/
theorem internFvar_run {k : Nat} {ty h : EIdx} {t : Expr} {s s' : AState}
    (hst : StateOK s) (hty : denoteE s.store ty = some t)
    (hrun : internE (.fvar k ty) s = .ok (h, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store h = some (.fvar k t) := by
  obtain ⟨hs, hd⟩ := Frontend.internE_sstep hst (viewOK_fvar (by rw [hty]; rfl)) hrun
  refine ⟨hs, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hty hs.ext, Option.map_some]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations — `ap1 n a`. -/
theorem natAp1_run {n : NIdx} {a h : EIdx} {nm : ConLeche.Name} {ea : Expr} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (ha : denoteE s.store a = some ea)
    (hrun : natAp1 n a s = .ok (h, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store h = some (.app (.const nm []) ea) := by
  simp only [Arena.natAp1] at hrun
  obtain ⟨f, s1, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hf⟩ := constE_run hst hp hn g1
  have ha1 := denote_ext ha hs1.ext
  obtain ⟨hs2, hd⟩ := Frontend.internE_sstep hs1.ok
    (viewOK_app (by rw [hf]; rfl) (by rw [ha1]; rfl)) k1
  refine ⟨hs1.trans hs2, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hf hs2.ext, denote_ext ha1 hs2.ext, opt2]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations — `ap2 n a b`. -/
theorem natAp2_run {n : NIdx} {a b h : EIdx} {nm : ConLeche.Name} {ea eb : Expr} {s s' : AState}
    (hst : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (ha : denoteE s.store a = some ea) (hb : denoteE s.store b = some eb)
    (hrun : natAp2 n a b s = .ok (h, s')) :
    Frontend.IStepS s s' ∧
      denoteE s'.store h = some (.app (.app (.const nm []) ea) eb) := by
  simp only [Arena.natAp2] at hrun
  obtain ⟨f, s1, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hf⟩ := natAp1_run hst hp hn ha g1
  have hb1 := denote_ext hb hs1.ext
  obtain ⟨hs2, hd⟩ := Frontend.internE_sstep hs1.ok
    (viewOK_app (by rw [hf]; rfl) (by rw [hb1]; rfl)) k1
  refine ⟨hs1.trans hs2, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hf hs2.ext, denote_ext hb1 hs2.ext, opt2]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpEquations) — the recurrence
equations, interned.

**PROVED** (task #97-P3-Checker round 8): seventeen shared links (pin reads,
`constE_run`, `internFvar_run`, `natAp1_run`) and one branch per operation of
`natAp1_run` / `natAp2_run`; the proof is generated text, every denotation
fact transported to the final state by the chain of `IStepS` behind it. -/
theorem natOpEquations_run {d : Nat} {cn : NIdx} {nm : ConLeche.Name}
    {eqs : List (EIdx × EIdx)} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpEquations d cn s = .ok (eqs, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      EqPairsDenote s'.store eqs (ConLeche.natOpEquations d nm) := by
  simp only [Arena.natOpEquations] at hr
  obtain ⟨v0, u0, q0, w0⟩ := AM.bind_ok hr
  obtain ⟨p0, d0⟩ := pinAt_run (x := ConLeche.natName) hp rfl q0
  rw [p0] at w0
  obtain ⟨v1, u1, q1, w1⟩ := AM.bind_ok w0
  obtain ⟨hs1, e1⟩ := constE_run hok hp d0 q1
  obtain ⟨v2, u2, q2, w2⟩ := AM.bind_ok w1
  obtain ⟨hs2, e2⟩ := internFvar_run (hs1).ok e1 q2
  obtain ⟨v3, u3, q3, w3⟩ := AM.bind_ok w2
  obtain ⟨hs3, e3⟩ := internFvar_run ((hs1).trans hs2).ok (denote_ext e1 (hs2.ext)) q3
  obtain ⟨v4, u4, q4, w4⟩ := AM.bind_ok w3
  obtain ⟨p4, d4⟩ := pinAt_run (x := ConLeche.natZeroName) (hp.mono (((hs1).trans hs2).trans hs3).ext (((hs1).trans hs2).trans hs3).pins) rfl q4
  rw [p4] at w4
  obtain ⟨v5, u5, q5, w5⟩ := AM.bind_ok w4
  obtain ⟨hs5, e5⟩ := constE_run (((hs1).trans hs2).trans hs3).ok (hp.mono (((hs1).trans hs2).trans hs3).ext (((hs1).trans hs2).trans hs3).pins) d4 q5
  obtain ⟨v6, u6, q6, w6⟩ := AM.bind_ok w5
  obtain ⟨p6, d6⟩ := pinAt_run (x := ConLeche.natSuccName) (hp.mono ((((hs1).trans hs2).trans hs3).trans hs5).ext ((((hs1).trans hs2).trans hs3).trans hs5).pins) rfl q6
  rw [p6] at w6
  obtain ⟨v7, u7, q7, w7⟩ := AM.bind_ok w6
  obtain ⟨hs7, e7⟩ := natAp1_run ((((hs1).trans hs2).trans hs3).trans hs5).ok (hp.mono ((((hs1).trans hs2).trans hs3).trans hs5).ext ((((hs1).trans hs2).trans hs3).trans hs5).pins) d6 (denote_ext e2 ((hs3.ext).trans hs5.ext)) q7
  obtain ⟨v8, u8, q8, w8⟩ := AM.bind_ok w7
  obtain ⟨hs8, e8⟩ := natAp1_run (((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).ok (hp.mono (((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).ext (((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).pins) (denoteN_ext d6 (hs7.ext)) (denote_ext e3 ((hs5.ext).trans hs7.ext)) q8
  obtain ⟨v9, u9, q9, w9⟩ := AM.bind_ok w8
  obtain ⟨p9, d9⟩ := pinAt_run (x := ConLeche.boolTrueName) (hp.mono ((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).ext ((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).pins) rfl q9
  rw [p9] at w9
  obtain ⟨v10, u10, q10, w10⟩ := AM.bind_ok w9
  obtain ⟨hs10, e10⟩ := constE_run ((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).ok (hp.mono ((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).ext ((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).pins) d9 q10
  obtain ⟨v11, u11, q11, w11⟩ := AM.bind_ok w10
  obtain ⟨p11, d11⟩ := pinAt_run (x := ConLeche.boolFalseName) (hp.mono (((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).ext (((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).pins) rfl q11
  rw [p11] at w11
  obtain ⟨v12, u12, q12, w12⟩ := AM.bind_ok w11
  obtain ⟨hs12, e12⟩ := constE_run (((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).ok (hp.mono (((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).ext (((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).pins) d11 q12
  obtain ⟨v13, u13, q13, w13⟩ := AM.bind_ok w12
  obtain ⟨p13, d13⟩ := pinAt_run (x := ConLeche.natPredName) (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) rfl q13
  rw [p13] at w13
  obtain ⟨v14, u14, q14, w14⟩ := AM.bind_ok w13
  obtain ⟨p14, d14⟩ := pinAt_run (x := ConLeche.natAddName) (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) rfl q14
  rw [p14] at w14
  obtain ⟨v15, u15, q15, w15⟩ := AM.bind_ok w14
  obtain ⟨p15, d15⟩ := pinAt_run (x := ConLeche.natSubName) (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) rfl q15
  rw [p15] at w15
  obtain ⟨v16, u16, q16, w16⟩ := AM.bind_ok w15
  obtain ⟨p16, d16⟩ := pinAt_run (x := ConLeche.natMulName) (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) rfl q16
  rw [p16] at w16
  obtain ⟨v17, u17, q17, w17⟩ := AM.bind_ok w16
  obtain ⟨p17, d17⟩ := pinAt_run (x := ConLeche.natPowName) (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) rfl q17
  rw [p17] at w17
  obtain ⟨v18, u18, q18, w18⟩ := AM.bind_ok w17
  obtain ⟨p18, d18⟩ := pinAt_run (x := ConLeche.natBeqName) (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) rfl q18
  rw [p18] at w18
  obtain ⟨v19, u19, q19, w19⟩ := AM.bind_ok w18
  obtain ⟨p19, d19⟩ := pinAt_run (x := ConLeche.natBleName) (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) rfl q19
  rw [p19] at w19
  have b_pr := beq_handle_iff ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok.wf (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) d13
  have b_ad := beq_handle_iff ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok.wf (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) d14
  have b_su := beq_handle_iff ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok.wf (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) d15
  have b_mu := beq_handle_iff ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok.wf (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) d16
  have b_po := beq_handle_iff ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok.wf (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) d17
  have b_be := beq_handle_iff ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok.wf (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) d18
  have b_bl := beq_handle_iff ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok.wf (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) d19
  rcases AM.ite_ok w19 with ⟨hc_pr, k_pr⟩ | ⟨hn_pr, k_pr⟩
  · obtain ⟨v20, u20, q20, w20⟩ := AM.bind_ok k_pr
    obtain ⟨hs20, e20⟩ := natAp1_run ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) q20
    obtain ⟨v21, u21, q21, w21⟩ := AM.bind_ok w20
    obtain ⟨hs21, e21⟩ := natAp1_run (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ok (hp.mono (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ext (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).pins) (denoteN_ext hn (((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e7 ((((hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) q21
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w21
    refine ⟨((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ok, ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ext, ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).caches, ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).pins, ?_⟩
    simp only [ConLeche.natOpEquations, if_pos (b_pr.mp hc_pr), EqPairsDenote]
    exact ⟨(denote_ext e20 (hs21.ext)), (denote_ext e5 ((((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)), e21, (denote_ext e2 ((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)), trivial⟩
  rcases AM.ite_ok k_pr with ⟨hc_ad, k_ad⟩ | ⟨hn_ad, k_ad⟩
  · obtain ⟨v20, u20, q20, w20⟩ := AM.bind_ok k_ad
    obtain ⟨hs20, e20⟩ := natAp2_run ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e2 ((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) q20
    obtain ⟨v21, u21, q21, w21⟩ := AM.bind_ok w20
    obtain ⟨hs21, e21⟩ := natAp2_run (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ok (hp.mono (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ext (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).pins) (denoteN_ext hn (((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e2 (((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e8 (((hs10.ext).trans hs12.ext).trans hs20.ext)) q21
    obtain ⟨v22, u22, q22, w22⟩ := AM.bind_ok w21
    obtain ⟨hs22, e22⟩ := natAp2_run ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ok (hp.mono ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ext ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).pins) (denoteN_ext hn ((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e2 ((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e3 (((((((hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) q22
    obtain ⟨v23, u23, q23, w23⟩ := AM.bind_ok w22
    obtain ⟨hs23, e23⟩ := natAp1_run (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ok (hp.mono (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ext (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).pins) (denoteN_ext d6 (((((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) e22 q23
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w23
    refine ⟨((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ok, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ext, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).caches, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).pins, ?_⟩
    simp only [ConLeche.natOpEquations, if_neg (fun h => hn_pr (b_pr.mpr h)), if_pos (b_ad.mp hc_ad), EqPairsDenote]
    exact ⟨(denote_ext e20 (((hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e2 ((((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e21 ((hs22.ext).trans hs23.ext)), e23, trivial⟩
  rcases AM.ite_ok k_ad with ⟨hc_su, k_su⟩ | ⟨hn_su, k_su⟩
  · obtain ⟨v20, u20, q20, w20⟩ := AM.bind_ok k_su
    obtain ⟨hs20, e20⟩ := natAp2_run ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e2 ((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) q20
    obtain ⟨v21, u21, q21, w21⟩ := AM.bind_ok w20
    obtain ⟨hs21, e21⟩ := natAp2_run (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ok (hp.mono (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ext (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).pins) (denoteN_ext hn (((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e2 (((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e8 (((hs10.ext).trans hs12.ext).trans hs20.ext)) q21
    obtain ⟨v22, u22, q22, w22⟩ := AM.bind_ok w21
    obtain ⟨hs22, e22⟩ := natAp2_run ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ok (hp.mono ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ext ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).pins) (denoteN_ext hn ((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e2 ((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e3 (((((((hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) q22
    obtain ⟨v23, u23, q23, w23⟩ := AM.bind_ok w22
    obtain ⟨hs23, e23⟩ := natAp1_run (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ok (hp.mono (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ext (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).pins) (denoteN_ext d13 (((hs20.ext).trans hs21.ext).trans hs22.ext)) e22 q23
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w23
    refine ⟨((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ok, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ext, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).caches, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).pins, ?_⟩
    simp only [ConLeche.natOpEquations, if_neg (fun h => hn_pr (b_pr.mpr h)), if_neg (fun h => hn_ad (b_ad.mpr h)), if_pos (b_su.mp hc_su), EqPairsDenote]
    exact ⟨(denote_ext e20 (((hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e2 ((((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e21 ((hs22.ext).trans hs23.ext)), e23, trivial⟩
  rcases AM.ite_ok k_su with ⟨hc_mu, k_mu⟩ | ⟨hn_mu, k_mu⟩
  · obtain ⟨v20, u20, q20, w20⟩ := AM.bind_ok k_mu
    obtain ⟨hs20, e20⟩ := natAp2_run ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e2 ((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) q20
    obtain ⟨v21, u21, q21, w21⟩ := AM.bind_ok w20
    obtain ⟨hs21, e21⟩ := natAp2_run (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ok (hp.mono (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ext (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).pins) (denoteN_ext hn (((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e2 (((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e8 (((hs10.ext).trans hs12.ext).trans hs20.ext)) q21
    obtain ⟨v22, u22, q22, w22⟩ := AM.bind_ok w21
    obtain ⟨hs22, e22⟩ := natAp2_run ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ok (hp.mono ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ext ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).pins) (denoteN_ext hn ((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e2 ((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e3 (((((((hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) q22
    obtain ⟨v23, u23, q23, w23⟩ := AM.bind_ok w22
    obtain ⟨hs23, e23⟩ := natAp2_run (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ok (hp.mono (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ext (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).pins) (denoteN_ext d14 (((hs20.ext).trans hs21.ext).trans hs22.ext)) e22 (denote_ext e2 (((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) q23
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w23
    refine ⟨((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ok, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ext, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).caches, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).pins, ?_⟩
    simp only [ConLeche.natOpEquations, if_neg (fun h => hn_pr (b_pr.mpr h)), if_neg (fun h => hn_ad (b_ad.mpr h)), if_neg (fun h => hn_su (b_su.mpr h)), if_pos (b_mu.mp hc_mu), EqPairsDenote]
    exact ⟨(denote_ext e20 (((hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e5 ((((((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e21 ((hs22.ext).trans hs23.ext)), e23, trivial⟩
  rcases AM.ite_ok k_mu with ⟨hc_po, k_po⟩ | ⟨hn_po, k_po⟩
  · obtain ⟨v20, u20, q20, w20⟩ := AM.bind_ok k_po
    obtain ⟨hs20, e20⟩ := natAp2_run ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e2 ((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) q20
    obtain ⟨v21, u21, q21, w21⟩ := AM.bind_ok w20
    obtain ⟨hs21, e21⟩ := natAp1_run (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ok (hp.mono (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ext (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).pins) (denoteN_ext d6 (((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e5 (((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) q21
    obtain ⟨v22, u22, q22, w22⟩ := AM.bind_ok w21
    obtain ⟨hs22, e22⟩ := natAp2_run ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ok (hp.mono ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ext ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).pins) (denoteN_ext hn ((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e2 ((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e8 ((((hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) q22
    obtain ⟨v23, u23, q23, w23⟩ := AM.bind_ok w22
    obtain ⟨hs23, e23⟩ := natAp2_run (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ok (hp.mono (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ext (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).pins) (denoteN_ext hn (((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) (denote_ext e2 (((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) (denote_ext e3 ((((((((hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) q23
    obtain ⟨v24, u24, q24, w24⟩ := AM.bind_ok w23
    obtain ⟨hs24, e24⟩ := natAp2_run ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ok (hp.mono ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ext ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).pins) (denoteN_ext d16 ((((hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)) e23 (denote_ext e2 ((((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)) q24
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w24
    refine ⟨(((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).ok, (((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).ext, (((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).caches, (((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).pins, ?_⟩
    simp only [ConLeche.natOpEquations, if_neg (fun h => hn_pr (b_pr.mpr h)), if_neg (fun h => hn_ad (b_ad.mpr h)), if_neg (fun h => hn_su (b_su.mpr h)), if_neg (fun h => hn_mu (b_mu.mpr h)), if_pos (b_po.mp hc_po), EqPairsDenote]
    exact ⟨(denote_ext e20 ((((hs21.ext).trans hs22.ext).trans hs23.ext).trans hs24.ext)), (denote_ext e21 (((hs22.ext).trans hs23.ext).trans hs24.ext)), (denote_ext e22 ((hs23.ext).trans hs24.ext)), e24, trivial⟩
  rcases AM.ite_ok k_po with ⟨hc_be, k_be⟩ | ⟨hn_be, k_be⟩
  · obtain ⟨v20, u20, q20, w20⟩ := AM.bind_ok k_be
    obtain ⟨hs20, e20⟩ := natAp2_run ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) q20
    obtain ⟨v21, u21, q21, w21⟩ := AM.bind_ok w20
    obtain ⟨hs21, e21⟩ := natAp2_run (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ok (hp.mono (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ext (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).pins) (denoteN_ext hn (((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e5 (((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e8 (((hs10.ext).trans hs12.ext).trans hs20.ext)) q21
    obtain ⟨v22, u22, q22, w22⟩ := AM.bind_ok w21
    obtain ⟨hs22, e22⟩ := natAp2_run ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ok (hp.mono ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ext ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).pins) (denoteN_ext hn ((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e7 (((((hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e5 ((((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) q22
    obtain ⟨v23, u23, q23, w23⟩ := AM.bind_ok w22
    obtain ⟨hs23, e23⟩ := natAp2_run (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ok (hp.mono (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ext (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).pins) (denoteN_ext hn (((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) (denote_ext e7 ((((((hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) (denote_ext e8 (((((hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) q23
    obtain ⟨v24, u24, q24, w24⟩ := AM.bind_ok w23
    obtain ⟨hs24, e24⟩ := natAp2_run ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ok (hp.mono ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ext ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).pins) (denoteN_ext hn ((((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)) (denote_ext e2 ((((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)) (denote_ext e3 (((((((((hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)) q24
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w24
    refine ⟨(((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).ok, (((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).ext, (((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).caches, (((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).trans hs24).pins, ?_⟩
    simp only [ConLeche.natOpEquations, if_neg (fun h => hn_pr (b_pr.mpr h)), if_neg (fun h => hn_ad (b_ad.mpr h)), if_neg (fun h => hn_su (b_su.mpr h)), if_neg (fun h => hn_mu (b_mu.mpr h)), if_neg (fun h => hn_po (b_po.mpr h)), if_pos (b_be.mp hc_be), EqPairsDenote]
    exact ⟨(denote_ext e20 ((((hs21.ext).trans hs22.ext).trans hs23.ext).trans hs24.ext)), (denote_ext e10 ((((((hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext).trans hs24.ext)), (denote_ext e21 (((hs22.ext).trans hs23.ext).trans hs24.ext)), (denote_ext e12 (((((hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext).trans hs24.ext)), (denote_ext e22 ((hs23.ext).trans hs24.ext)), (denote_ext e12 (((((hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext).trans hs24.ext)), (denote_ext e23 (hs24.ext)), e24, trivial⟩
  rcases AM.ite_ok k_be with ⟨hc_bl, k_bl⟩ | ⟨hn_bl, k_bl⟩
  · obtain ⟨v20, u20, q20, w20⟩ := AM.bind_ok k_bl
    obtain ⟨hs20, e20⟩ := natAp2_run ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok (hp.mono ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins) (denoteN_ext hn ((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e5 ((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) (denote_ext e3 (((((hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext)) q20
    obtain ⟨v21, u21, q21, w21⟩ := AM.bind_ok w20
    obtain ⟨hs21, e21⟩ := natAp2_run (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ok (hp.mono (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).ext (((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).pins) (denoteN_ext hn (((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e7 ((((hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) (denote_ext e5 (((((hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext)) q21
    obtain ⟨v22, u22, q22, w22⟩ := AM.bind_ok w21
    obtain ⟨hs22, e22⟩ := natAp2_run ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ok (hp.mono ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).ext ((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).pins) (denoteN_ext hn ((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e7 (((((hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) (denote_ext e8 ((((hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext)) q22
    obtain ⟨v23, u23, q23, w23⟩ := AM.bind_ok w22
    obtain ⟨hs23, e23⟩ := natAp2_run (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ok (hp.mono (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).ext (((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).pins) (denoteN_ext hn (((((((((((hs1.ext).trans hs2.ext).trans hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) (denote_ext e2 (((((((((hs3.ext).trans hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) (denote_ext e3 ((((((((hs5.ext).trans hs7.ext).trans hs8.ext).trans hs10.ext).trans hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext)) q23
    obtain ⟨rfl, rfl⟩ := AM.pure_ok w23
    refine ⟨((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ok, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).ext, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).caches, ((((((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).trans hs20).trans hs21).trans hs22).trans hs23).pins, ?_⟩
    simp only [ConLeche.natOpEquations, if_neg (fun h => hn_pr (b_pr.mpr h)), if_neg (fun h => hn_ad (b_ad.mpr h)), if_neg (fun h => hn_su (b_su.mpr h)), if_neg (fun h => hn_mu (b_mu.mpr h)), if_neg (fun h => hn_po (b_po.mpr h)), if_neg (fun h => hn_be (b_be.mpr h)), if_pos (b_bl.mp hc_bl), EqPairsDenote]
    exact ⟨(denote_ext e20 (((hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e10 (((((hs12.ext).trans hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e21 ((hs22.ext).trans hs23.ext)), (denote_ext e12 ((((hs20.ext).trans hs21.ext).trans hs22.ext).trans hs23.ext)), (denote_ext e22 (hs23.ext)), e23, trivial⟩
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k_bl
  refine ⟨((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ok, ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).ext, ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).caches, ((((((((hs1).trans hs2).trans hs3).trans hs5).trans hs7).trans hs8).trans hs10).trans hs12).pins, ?_⟩
  simp only [ConLeche.natOpEquations, if_neg (fun h => hn_pr (b_pr.mpr h)), if_neg (fun h => hn_ad (b_ad.mpr h)), if_neg (fun h => hn_su (b_su.mpr h)), if_neg (fun h => hn_mu (b_mu.mpr h)), if_neg (fun h => hn_po (b_po.mpr h)), if_neg (fun h => hn_be (b_be.mpr h)), if_neg (fun h => hn_bl (b_bl.mpr h)), EqPairsDenote]


/-- con-leche: ConLeche/Kernel/CoreDefs.lean:614-620 Expr.substConst0 — the
spine substitution over handles is con-leche's: `.const n []` is a handle
comparison against the pinned empty level list, and the `app` arm re-interns. -/
theorem substConst0_run {cn : NIdx} {nm : ConLeche.Name} {rh : EIdx} {x : Expr} :
    ∀ (fuel : Nat) {h h' : EIdx} {e : Expr} {s s' : AState}, StateOK s →
      PinsOK s → denoteN s.store.ns cn = some nm → denoteE s.store rh = some x →
      denoteE s.store h = some e →
      Arena.substConst0 cn rh fuel h s = .ok (h', s') →
      Frontend.IStepS s s' ∧
        denoteE s'.store h' = some (Expr.substConst0 nm x e) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h h' e s s' _ _ _ _ _ hrun
    exact absurd hrun (AM.Never.fail _ _ _ _)
  | succ fuel ih =>
    intro h h' e s s' hst hp hn hx he hrun
    have hwf := hst.wf
    have hwf' := hwf
    obtain ⟨rk, hrk⟩ := hwf'
    simp only [Arena.substConst0] at hrun
    obtain ⟨v, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨e1s, hv⟩ := viewE_run g1
    rw [e1s] at k1
    cases v
    case const c us =>
      obtain ⟨cN, ls, rfl, hcN, hls⟩ := denote_const_inv hwf hv he
      obtain ⟨el, s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨e2s, hel⟩ := AM.of_run (P := fun t => t = s)
        (Q := fun r t => t = s ∧ denoteLs s.store.lss r = some []) rfl g2
        (pinEmptyLevels_spec s hp)
      rw [e2s] at k2
      have e1 := beq_of_denote_inj (fun h1 h2 => denoteN_inj hrk.nsWF h1 h2) hcN hn
      have e2 := beq_of_denote_inj (fun h1 h2 => denoteLs_inj hrk.lss h1 h2) hls hel
      rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        simp only [Bool.and_eq_true, e1, e2, beq_iff_eq] at hc
        refine ⟨Frontend.IStepS.refl hst, ?_⟩
        simp only [Expr.substConst0, hc, and_self, if_true]
        exact hx
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        simp only [Bool.and_eq_true, e1, e2, beq_iff_eq] at hc
        refine ⟨Frontend.IStepS.refl hst, ?_⟩
        simp only [Expr.substConst0, if_neg hc]
        exact he
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hv he
      obtain ⟨f', s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, hf'⟩ := ih hst hp hn hx hf g2
      obtain ⟨a', s3, g3, k3⟩ := AM.bind_ok k2
      obtain ⟨hs3, ha'⟩ := ih hs2.ok (hp.mono hs2.ext hs2.pins)
        (denoteN_ext hn hs2.ext) (denote_ext hx hs2.ext) (denote_ext ha hs2.ext) g3
      have hf3 := denote_ext hf' hs3.ext
      obtain ⟨hs4, hd⟩ := Frontend.internE_sstep hs3.ok
        (viewOK_app (by rw [hf3]; rfl) (by rw [ha']; rfl)) k3
      refine ⟨(hs2.trans hs3).trans hs4, ?_⟩
      rw [hd]
      simp only [denoteEView, denote_ext hf3 hs4.ext, denote_ext ha' hs4.ext, opt2,
        Expr.substConst0]
    all_goals first
      | (obtain rfl := denote_bvar_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, rfl, _⟩ := denote_fvar_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, rfl, _⟩ := denote_sort_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, _, rfl, _⟩ := denote_lam_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, _, rfl, _⟩ := denote_forallE_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, _, _, rfl, _⟩ := denote_letE_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain rfl := denote_lit_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)
      | (obtain ⟨_, _, rfl, _⟩ := denote_proj_inv hwf hv he
         obtain ⟨rfl, rfl⟩ := AM.pure_ok k1; exact ⟨Frontend.IStepS.refl hst, he⟩)

/-- con-leche: ConLeche/Kernel/ExprOps.lean (Expr.substConst0) — the
self-reference substitution, pair by pair.

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4):
`substConst0`'s `.const` arm reads `emptyLevels` and compares the stored
universe-argument handle against it, so without the pin invariant nothing
ties that comparison to con-leche's `us = []`.  Free at the one call site
(`hok7.check.pins`).

**PROVED** (task #97-P3-Checker round 8): a list recursion over
`substConst0_run`. -/
theorem substConst0Pairs_run {cn : NIdx} {nm : ConLeche.Name} {rh : EIdx}
    {x : Expr} {eqs r : List (EIdx × EIdx)} {xs : List (Expr × Expr)}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns cn = some nm)
    (hv : denoteE s.store rh = some x) (hd : EqPairsDenote s.store eqs xs)
    (hr : substConst0Pairs cn rh eqs s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      EqPairsDenote s'.store r
        (xs.map fun eq => (Expr.substConst0 nm x eq.1,
          Expr.substConst0 nm x eq.2)) := by
  suffices h : ∀ (eqs : List (EIdx × EIdx)) (xs : List (Expr × Expr))
      {r : List (EIdx × EIdx)} {s s' : AState}, StateOK s → PinsOK s →
      denoteN s.store.ns cn = some nm → denoteE s.store rh = some x →
      EqPairsDenote s.store eqs xs → substConst0Pairs cn rh eqs s = .ok (r, s') →
      Frontend.IStepS s s' ∧ EqPairsDenote s'.store r
        (xs.map fun eq => (Expr.substConst0 nm x eq.1,
          Expr.substConst0 nm x eq.2)) by
    obtain ⟨hs, hd'⟩ := h eqs xs hok hp hn hv hd hr
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, hd'⟩
  intro eqs
  induction eqs with
  | nil =>
    intro xs r s s' hst _ _ _ hd hr
    cases xs with
    | cons q qs => exact absurd hd (by simp [EqPairsDenote])
    | nil =>
      simp only [Arena.substConst0Pairs] at hr
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr
      exact ⟨Frontend.IStepS.refl hst, trivial⟩
  | cons e es ih =>
    intro xs r s s' hst hp hn hv hd hr
    cases xs with
    | nil => exact absurd hd (by simp [EqPairsDenote])
    | cons q qs =>
      obtain ⟨hd1, hd2, hdt⟩ := hd
      obtain ⟨a, b⟩ := e
      simp only [Arena.substConst0Pairs] at hr
      obtain ⟨a', s1, g1, k1⟩ := AM.bind_ok hr
      obtain ⟨hs1, ha⟩ := substConst0_run _ hst hp hn hv hd1 g1
      obtain ⟨b', s2, g2, k2⟩ := AM.bind_ok k1
      obtain ⟨hs2, hb⟩ := substConst0_run _ hs1.ok (hp.mono hs1.ext hs1.pins)
        (denoteN_ext hn hs1.ext) (denote_ext hv hs1.ext) (denote_ext hd2 hs1.ext) g2
      obtain ⟨rest, s3, g3, k3⟩ := AM.bind_ok k2
      have hs12 := hs1.trans hs2
      obtain ⟨hs3, hrest⟩ := ih qs hs12.ok (hp.mono hs12.ext hs12.pins)
        (denoteN_ext hn hs12.ext) (denote_ext hv hs12.ext)
        (EqPairsDenote.mono hs12.ext hdt) g3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
      refine ⟨hs12.trans hs3, ?_⟩
      exact ⟨denote_ext (denote_ext ha hs2.ext) hs3.ext, denote_ext hb hs3.ext, hrest⟩



/-- con-leche: ConLeche/Kernel/Checker.lean:110-125 certifyNatEqs — the
recurrence equations, certified by definitional equality in the pre-insertion
environment.

**PROVED** (task #97-P3-Checker round 5): a list induction over
`KnotSpec.defeq`, at `Bridge/Checker/Base.lean`'s `checkDefEqList_bridge`
shape — one `max` over the head's fuel and the tail's, `isDefEqCore_mono` and
`certifyNatEqs_mono` to raise each.  The equations' own exactness
(`natOpEquations_run`, `substConst0Pairs_run`) is NOT part of it: this theorem
takes the pairing as `hden` and the well-scopedness as `hws`, so it is
independent of how the pinned terms were built.  Task #97-P3-Checker's sorry
list, item 23, closed. -/
theorem certifyNatEqs_bridge_aux {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) :
    ∀ (eqs : List (EIdx × EIdx)) (xs : List (Expr × Expr)) (r : Bool)
      (s s' : AState), CheckOK μ env fe s → EqPairsDenote s.store eqs xs →
      (∀ q ∈ xs, Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2) →
      certifyNatEqs μ fe eqs s = .ok (r, s') →
      CoreStep μ env fe s s' ∧
        (r = true → ∃ F, ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env xs
          = .ok true) := by
  have hknot := hk.knot env fe henv
  intro eqs
  induction eqs with
  | nil =>
    intro xs r s s' hok hden _ hrun
    cases xs with
    | cons q qs => exact absurd hden (by simp [EqPairsDenote])
    | nil =>
      simp only [Arena.certifyNatEqs] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CoreStep.refl hok, fun _ => ⟨0, rfl⟩⟩
  | cons e es ih =>
    intro xs r s s' hok hden hws hrun
    cases xs with
    | nil => exact absurd hden (by simp [EqPairsDenote])
    | cons q qs =>
      obtain ⟨hd1, hd2, hdt⟩ := hden
      obtain ⟨hw1, hw2⟩ := hws q (by simp)
      simp only [Arena.certifyNatEqs] at hrun
      obtain ⟨b1, s1, g1, r1⟩ := AM.bind_ok hrun
      obtain ⟨hok1, hx1, hp1, hsim1⟩ := AM.of_run (P := fun u => u = s)
        (Q := fun x u => CheckOK μ env fe u ∧ Ext s.store u.store ∧
          u.pins = s.pins ∧
          Core.SimV (ConLeche.isDefEqCore μ env) 2 q.1 q.2 x)
        rfl g1 (hknot.defeq s 2 e.1 e.2 q.1 q.2 hok hd1 hd2 hw1 hw2)
      obtain ⟨F1, hF1⟩ := hsim1
      rcases AM.ite_ok r1 with ⟨hb, r2⟩ | ⟨hb, r2⟩
      · subst hb
        obtain ⟨hstep2, hpure2⟩ := ih qs r s1 s' hok1
          (EqPairsDenote.mono hx1 hdt)
          (fun z hz => hws z (by simp [hz])) r2
        refine ⟨⟨hstep2.ok, hx1.trans hstep2.ext, by rw [hstep2.pins, hp1]⟩,
          fun hr => ?_⟩
        obtain ⟨F2, hF2⟩ := hpure2 hr
        refine ⟨max F1 F2, ?_⟩
        exact certifyNatEqs_cons_pure
          (ConLeche.isDefEqCore_mono (Nat.le_max_left F1 F2) hF1)
          (certifyNatEqs_mono (Nat.le_max_right F1 F2) hF2)
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
        exact ⟨⟨hok1, hx1, hp1⟩, fun hr => absurd hr (by simp)⟩

theorem certifyNatEqs_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {eqs : List (EIdx × EIdx)} {xs : List (Expr × Expr)}
    {r : Bool} {s s' : AState} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (hok : FoldOK μ env fe s)
    (hden : EqPairsDenote s.store eqs xs)
    (hws : ∀ q ∈ xs, Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2)
    (hrun : certifyNatEqs μ fe eqs s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧
      (r = true → ∃ F, ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env xs
        = .ok true) :=
  certifyNatEqs_bridge_aux hk hok.envWF eqs xs r s s' hok.check hden hws hrun

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:614-620 Expr.substConst0 — the
spine substitution preserves scoping at a scoped replacement. -/
theorem substConst0_wscoped {n : ConLeche.Name} {r : Expr} {d : Nat}
    (hr : Expr.WScoped d r) :
    ∀ e, Expr.WScoped d e → Expr.WScoped d (Expr.substConst0 n r e) := by
  intro e
  induction e
  case const c us =>
    intro h
    simp only [Expr.substConst0]
    split
    · exact hr
    · exact h
  case app f a ihf iha =>
    intro h
    simp only [Expr.substConst0]
    unfold Expr.WScoped at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  all_goals (intro h; exact h)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations — every
side of every equation is scoped at depth 2 (`fvar 0`, `fvar 1` at `Nat`). -/
theorem natOpEquations_wscoped (nm : ConLeche.Name) :
    ∀ q ∈ ConLeche.natOpEquations 0 nm,
      Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2 := by
  intro q hq
  unfold ConLeche.natOpEquations at hq
  simp only at hq
  repeat' split at hq
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    repeat' rcases hq with rfl | hq
  all_goals first
    | simp [Expr.WScoped]
    | exact absurd hq (by simp)

/-- con-leche: ConLeche/Kernel/Checker.lean:110-125 certifyNatEqs — the
substituted recurrence equations are well scoped at the depth the certifier
runs them at (`isDefEq … 2`: the equations' variables are `fvar 0` and
`fvar 1`).  A pure fact about con-leche's own pinned construction, which
`certifyNatEqs_bridge`'s `KnotSpec.defeq` calls need as their precondition.

**PROVED** (task #97-P3-Checker round 8): `natOpEquations_wscoped` (the
literal shapes, by cases) and `substConst0_wscoped` at the stored value,
which `EnvWF env2`'s `defnInfo` clause makes free of free variables. -/
theorem natOpEqs_wscoped {env2 : Env} {nm : ConLeche.Name}
    {cv' : ConstantVal} {v' : Expr} {hint' : ReducibilityHint}
    (henv : EnvWF env2)
    (hf : env2.find? nm = some (.defnInfo cv' v' hint')) :
    ∀ q ∈ (ConLeche.natOpEquations 0 nm).map
      (fun eq => (Expr.substConst0 nm v' eq.1, Expr.substConst0 nm v' eq.2)),
      Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2 := by
  intro q hq
  have hc := henv _ (List.mem_of_find?_eq_some hf)
  obtain ⟨hf1, -, -, -⟩ := hc.2.2.2.2.1 cv' v' hint' rfl
  have hv2 : Expr.WScoped 2 v' := ConLeche.Expr.WScoped.of_not_hasFvar hf1
  simp only [List.mem_map] at hq
  obtain ⟨eq, heq, rfl⟩ := hq
  obtain ⟨h1, h2⟩ := natOpEquations_wscoped nm eq heq
  exact ⟨substConst0_wscoped hv2 _ h1, substConst0_wscoped hv2 _ h2⟩

/-! ## The two pinned-variant gates -/

/-! ## The `Nat.div`/`Nat.mod` variant gate, skeletonised (round 9)

`checkDivModPin` is an environment guard, a lookup of the stored value, and
the variant loop; the loop's step is two syntactic guards and one ATTEMPT
under `orElseAttempt`.  The proof below reads that structure and names the
four pieces it does not prove: the three guards' exactness and the attempt's.

**The loop needs only the `true` direction of each piece.**  Every outcome
but `matched` moves the arena to the next variant, and con-leche's
`(fueledOps μ F).orElse x k` is `match x with | .ok true => pure () | _ => k
none` (`fueledOps_orElse`): whether the pure side's guards or attempt agree or
not, it either stops with `.ok ()` or recurses — and the recursion is the
induction hypothesis, at the SAME fuel.  Only the `matched` step has to line
the two sides up: guards `true` and the pure attempt `.ok true`. -/

/-- con-leche: none — a stored constant's TYPE compared against an interned
expression, as a guard in front of a continuation (`divModEnvGuard`'s `Bool.true`
lookup). -/
theorem RunsB.matchTyAnd {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    (hpn : ∀ ci, x = some ci → Frontend.CIProjNamed s.store ci)
    {ty : EIdx} {T : Expr} (hty : denoteE s.store ty = some T)
    {Y : AM Bool} {B : Bool}
    (hY : ∀ {s₁ : AState}, Frontend.IStepS s s₁ → RunsB Y s₁ B) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv ← ci.toConstantVal
          if (cv.type != ty) = true then pure false else Y
        | none => pure false) s
      ((match (generalizing := false) y with
        | some ci => ci.toConstantVal.type == T
        | none => false) && B) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (hpn ci rfl) hd g1
    refine ⟨hs1, ?_⟩
    obtain ⟨-, -, hvt⟩ := denoteCV_inv hv
    exact RunsB.guard hs1.ok
      (by simp only [bne, beqE_of_denote hs1.ok.wf hvt (denote_ext hty hs1.ext)])
      fun _ => hY hs1

/-- con-leche: none — the same comparison as the chain's last link
(`divModEnvGuard`'s `Bool.false` lookup). -/
theorem RunsB.matchTy {x : Option IConstantInfo} {y : Option ConstantInfo}
    {s : AState} (hok : StateOK s) (hxy : FindRel s.store x y)
    (hpn : ∀ ci, x = some ci → Frontend.CIProjNamed s.store ci)
    {ty : EIdx} {T : Expr} (hty : denoteE s.store ty = some T) :
    RunsB (match (generalizing := false) x with
        | some ci => do
          let cv ← ci.toConstantVal
          pure (cv.type == ty)
        | none => pure false) s
      (match (generalizing := false) y with
        | some ci => ci.toConstantVal.type == T
        | none => false) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨ci, c, rfl, rfl, hd⟩
  · exact RunsB.ret hok
  · refine RunsB.bind fun {v s₁} g1 => ?_
    obtain ⟨hs1, hv⟩ := toConstantVal_sstep hok (hpn ci rfl) hd g1
    refine ⟨hs1, ?_⟩
    obtain ⟨-, -, hvt⟩ := denoteCV_inv hv
    rw [beqE_of_denote hs1.ok.wf hvt (denote_ext hty hs1.ext)]
    exact RunsB.ret hs1.ok

/-- con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard — the
environment prerequisites, read at the extended environment.

**PROVED** (task #97-P3-Checker round 10): `natOpGuard_runsB`,
`natOpDeps_run` + `natOpStoredOkAll_runs`, the `fe2.find? en == some eqA` test
(`IFEnvOK.find_beq_ind` at the freshly interned `eqA`), and the two `Bool`
constructors' types (`RunsB.matchTyAnd`, `RunsB.matchTy`) against the interned
`.const Bool []`. -/
theorem divModEnvGuard_run {env2 : Env} {fe2 : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s) (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns cn = some nm)
    (hr : Arena.divModEnvGuard fe2 cn s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.divModEnvGuard env2 nm := by
  suffices h : RunsB (Arena.divModEnvGuard fe2 cn) s (ConLeche.divModEnvGuard env2 nm) by
    obtain ⟨hs, rfl⟩ := h _ _ hr
    exact ⟨hs.ok, hs.ext, hs.caches, hs.pins, rfl⟩
  have tr : ∀ {t : AState}, Frontend.IStepS s t →
      StateOK t ∧ PinsOK t ∧ IFEnvOK env2 fe2 t ∧ denoteN t.store.ns cn = some nm :=
    fun ht => ⟨ht.ok, hp.mono ht.ext ht.pins, hie.mono ht.ext, denoteN_ext hn ht.ext⟩
  simp only [ConLeche.divModEnvGuard, Bool.and_assoc]
  unfold Arena.divModEnvGuard
  refine RunsB.bindB (natOpGuard_runsB hok hp hie hn) fun {s1} hs1 => ?_
  obtain ⟨st1, hp1, hie1, hn1⟩ := tr hs1
  refine RunsB.guard st1 (by simp) fun _ => ?_
  refine RunsB.bind fun {ds s2} g2 => ?_
  obtain rfl := natOpDeps_state hp1 g2
  obtain ⟨-, -, -, -, hds⟩ := natOpDeps_run st1 hp1 hn1 g2
  refine ⟨Frontend.IStepS.refl st1, ?_⟩
  refine RunsB.bindB (natOpStoredOkAll_runs ds _ st1 hp1 hie1 hds) fun {s3} hs3 => ?_
  obtain ⟨st3, hp3, hie3, -⟩ := tr (hs1.trans hs3)
  refine RunsB.guard st3 (by simp) fun _ => ?_
  refine RunsB.pin st3 hp3 (x := ConLeche.eqName) (by rfl) fun en den => ?_
  refine RunsB.bind fun {ea s4} g4 => ?_
  obtain ⟨hs4, hea, -⟩ := internCI_fresh st3 g4
  refine ⟨hs4, ?_⟩
  obtain ⟨st4, hp4, hie4, -⟩ := tr ((hs1.trans hs3).trans hs4)
  obtain ⟨cvE, dE, hE⟩ : ∃ cv d, ConLeche.eqA = .indInfo cv d := ⟨_, _, rfl⟩
  rw [hE] at hea ⊢
  refine RunsB.guard st4 (by
    rw [bne, hie4.find_beq_ind st4 (denoteN_ext den hs4.ext) hea]
    cases env2.find? eqName <;> (try simp) <;> rfl) fun _ => ?_
  refine RunsB.pin st4 hp4 (x := ConLeche.boolName) (by rfl) fun bn dbn => ?_
  refine RunsB.bind fun {bty s5} g5 => ?_
  obtain ⟨hs5, hbty⟩ := constE_run st4 hp4 dbn g5
  refine ⟨hs5, ?_⟩
  obtain ⟨st5, hp5, hie5, -⟩ := tr (((hs1.trans hs3).trans hs4).trans hs5)
  refine RunsB.pin st5 hp5 (x := ConLeche.boolTrueName) (by rfl) fun bt dbt => ?_
  refine RunsB.matchTyAnd st5 (hie5.findRel st5 dbt)
    (fun ci hf => CIProjNamed_of_find hie5 hf) hbty fun {s6} hs6 => ?_
  have hie6 := hie5.mono hs6.ext
  refine RunsB.pin hs6.ok (hp5.mono hs6.ext hs6.pins) (x := ConLeche.boolFalseName)
    (by rfl) fun bf dbf => ?_
  exact RunsB.matchTy hs6.ok (hie6.findRel hs6.ok dbf)
    (fun ci hf => CIProjNamed_of_find hie6 hf) (denote_ext hbty hs6.ext)

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:209-213 reducePinGuard
con-leche: ConLeche/Kernel/Checker.lean:292-297 divModPinGuard — **the four
syntactic guards on an interned pin** (bounded, closed, level-monomorphic,
resolving), as the two pin guards share them: the Fast walks answer
con-leche's `Bool`s at the pin's denotation.  (Task #97-P3-Checker round 10
lifted it out of `reducePinGuard_run`, whose tail it was.) -/
theorem pinGuardWalk_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {p : EIdx} {E : Expr} {r : Bool} {s s1 s' : AState}
    (hck1 : CheckOK μ env fe s1) (hs1x : Ext s.store s1.store)
    (hs1p : s1.pins = s.pins) (hpd : denoteE s1.store p = some E)
    (r1 : (do
        if !(← looseBVarsBoundedFast coreWalkFuel 0 p) then pure false
        else if ← hasFvarFast coreWalkFuel p then pure false
        else if !(← allLevelParamsDefined [] p) then pure false
        else constsResolveFFast fe p : AM Bool) s1 = .ok (r, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      r = (E.looseBVarsBounded 0 && (!E.hasFvar &&
        (E.allLevelParamsDefined [] && E.constsResolve env))) := by
  have frame : ∀ {t : AState}, t.store = s1.store → t.caches = s1.caches →
      t.pins = s1.pins → CheckOK μ env fe t ∧ Ext s.store t.store ∧
        t.pins = s.pins := fun h1 h2 h3 =>
    ⟨hck1.mono ⟨by rw [h1]; exact hck1.state.wf⟩ (by rw [h1]; exact Ext.refl _)
      h2 h3, by rw [h1]; exact hs1x, by rw [h3, hs1p]⟩
  obtain ⟨b2, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨h2st, h2c, h2p, h2r⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => t.store = s1.store ∧ t.caches = s1.caches ∧
      t.pins = s1.pins ∧ RelV (Expr.looseBVarsBounded 0) s1.store p r)
    rfl g2 (ConRon.Bridge.ExprOps.looseBVarsBoundedFast_spec coreWalkFuel 0 s1
      p hck1.state (by rw [hpd]; rfl))
  have e2 := h2r _ hpd
  rcases AM.ite_ok r2 with ⟨hc2, k2⟩ | ⟨hc2, k2⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
    obtain ⟨a, b, c⟩ := frame h2st h2c h2p
    refine ⟨a, b, c, ?_⟩
    simp only [Bool.not_eq_true'] at hc2
    rw [← e2, hc2, Bool.false_and]
  have hc2' : b2 = true := by simpa using hc2
  obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok k2
  have hp2 : denoteE s2.store p = some (E) := by
    rw [h2st]; exact hpd
  obtain ⟨h3st, h3c, h3p, h3r⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => t.store = s2.store ∧ t.caches = s2.caches ∧
      t.pins = s2.pins ∧ RelV Expr.hasFvar s2.store p r)
    rfl g3 (ConRon.Bridge.ExprOps.hasFvarFast_spec coreWalkFuel s2 p
      (frame h2st h2c h2p).1.state (by rw [hp2]; rfl))
  have e3 := h3r _ hp2
  have f3 : s3.store = s1.store := by rw [h3st, h2st]
  have c3 : s3.caches = s1.caches := by rw [h3c, h2c]
  have q3 : s3.pins = s1.pins := by rw [h3p, h2p]
  rcases AM.ite_ok r3 with ⟨hc3, k3⟩ | ⟨hc3, k3⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
    obtain ⟨a, b, c⟩ := frame f3 c3 q3
    refine ⟨a, b, c, ?_⟩
    rw [← e2, hc2', ← e3, hc3]; rfl
  have hc3' : b3 = false := by simpa using hc3
  obtain ⟨b4, s4, g4, r4⟩ := AM.bind_ok k3
  have hp3 : denoteE s3.store p = some (E) := by
    rw [f3]; exact hpd
  obtain ⟨h4st, h4c, h4p, h4r⟩ :=
    allLevelParamsDefined_run (frame f3 c3 q3).1.state rfl hp3 g4
  have f4 : s4.store = s1.store := by rw [h4st, f3]
  have c4 : s4.caches = s1.caches := by rw [h4c, c3]
  have q4 : s4.pins = s1.pins := by rw [h4p, q3]
  rcases AM.ite_ok r4 with ⟨hc4, k4⟩ | ⟨hc4, k4⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
    obtain ⟨a, b, c⟩ := frame f4 c4 q4
    refine ⟨a, b, c, ?_⟩
    simp only [Bool.not_eq_true'] at hc4
    rw [← e2, hc2', ← e3, hc3', ← h4r, hc4]; rfl
  have hc4' : b4 = true := by simpa using hc4
  have hp4 : denoteE s4.store p = some (E) := by
    rw [f4]; exact hpd
  obtain ⟨h5st, h5c, h5p, h5r⟩ :=
    constsResolveFFast_run (frame f4 c4 q4).1 hp4 k4
  obtain ⟨a, b, c⟩ := frame (by rw [h5st, f4]) (by rw [h5c, c4]) (by rw [h5p, q4])
  refine ⟨a, b, c, ?_⟩
  rw [← e2, hc2', ← e3, hc3', ← h4r, hc4', ← h5r]; rfl


/-- con-leche: ConLeche/Kernel/Checker.lean:122-130 divModDeclPin — one
variant's pinned defining expression: seven pin reads and handle tests, each
con-leche's name test (`beq_handle_iff`), and the variant's field. -/
theorem divModDeclPin_run {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx}
    {nm : ConLeche.Name} {p : EIdx} {s s' : AState} (hst : StateOK s)
    (hp : PinsOK s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : Arena.divModDeclPin ps cn s = .ok (p, s')) :
    s' = s ∧ denoteE s.store p = some (ConLeche.divModDeclPin psP nm) := by
  simp only [Arena.divModDeclPin] at hrun
  obtain ⟨h0, u0, g0, w0⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d0⟩ := pinAt_run (x := ConLeche.natDivName) hp (by rfl) g0
  have b0 := beq_handle_iff hst.wf hn d0
  rcases AM.ite_ok w0 with ⟨y0, a0⟩ | ⟨z0, v0⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a0
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_pos (b0.mp y0)]
    exact hps.divPin
  have nb0 : ¬ (nm = ConLeche.natDivName) := fun h => z0 (b0.mpr h)
  obtain ⟨h1, u1, g1, w1⟩ := AM.bind_ok v0
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natGcdName) hp (by rfl) g1
  have b1 := beq_handle_iff hst.wf hn d1
  rcases AM.ite_ok w1 with ⟨y1, a1⟩ | ⟨z1, v1⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a1
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_pos (b1.mp y1)]
    exact hps.gcdPin
  have nb1 : ¬ (nm = ConLeche.natGcdName) := fun h => z1 (b1.mpr h)
  obtain ⟨h2, u2, g2, w2⟩ := AM.bind_ok v1
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natLandName) hp (by rfl) g2
  have b2 := beq_handle_iff hst.wf hn d2
  rcases AM.ite_ok w2 with ⟨y2, a2⟩ | ⟨z2, v2⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a2
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_pos (b2.mp y2)]
    exact hps.landPin
  have nb2 : ¬ (nm = ConLeche.natLandName) := fun h => z2 (b2.mpr h)
  obtain ⟨h3, u3, g3, w3⟩ := AM.bind_ok v2
  obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natLorName) hp (by rfl) g3
  have b3 := beq_handle_iff hst.wf hn d3
  rcases AM.ite_ok w3 with ⟨y3, a3⟩ | ⟨z3, v3⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a3
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_pos (b3.mp y3)]
    exact hps.lorPin
  have nb3 : ¬ (nm = ConLeche.natLorName) := fun h => z3 (b3.mpr h)
  obtain ⟨h4, u4, g4, w4⟩ := AM.bind_ok v3
  obtain ⟨rfl, d4⟩ := pinAt_run (x := ConLeche.natXorName) hp (by rfl) g4
  have b4 := beq_handle_iff hst.wf hn d4
  rcases AM.ite_ok w4 with ⟨y4, a4⟩ | ⟨z4, v4⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a4
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_pos (b4.mp y4)]
    exact hps.xorPin
  have nb4 : ¬ (nm = ConLeche.natXorName) := fun h => z4 (b4.mpr h)
  obtain ⟨h5, u5, g5, w5⟩ := AM.bind_ok v4
  obtain ⟨rfl, d5⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp (by rfl) g5
  have b5 := beq_handle_iff hst.wf hn d5
  rcases AM.ite_ok w5 with ⟨y5, a5⟩ | ⟨z5, v5⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a5
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_pos (b5.mp y5)]
    exact hps.shiftLeftPin
  have nb5 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z5 (b5.mpr h)
  obtain ⟨h6, u6, g6, w6⟩ := AM.bind_ok v5
  obtain ⟨rfl, d6⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp (by rfl) g6
  have b6 := beq_handle_iff hst.wf hn d6
  rcases AM.ite_ok w6 with ⟨y6, a6⟩ | ⟨z6, v6⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a6
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_pos (b6.mp y6)]
    exact hps.shiftRightPin
  have nb6 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z6 (b6.mpr h)
  obtain ⟨rfl, rfl⟩ := AM.pure_ok v6
  refine ⟨rfl, ?_⟩
  rw [ConLeche.divModDeclPin, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6]
  exact hps.modPin

/-- con-leche: ConLeche/Kernel/Checker.lean:134-142 divModCertProofs — one
variant's certificate proofs, by the same seven tests. -/
theorem divModCertProofs_run {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx}
    {nm : ConLeche.Name} {p : List EIdx} {s s' : AState} (hst : StateOK s)
    (hp : PinsOK s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : Arena.divModCertProofs ps cn s = .ok (p, s')) :
    s' = s ∧ Frontend.denoteEList s.store p = some (ConLeche.divModCertProofs psP nm) := by
  simp only [Arena.divModCertProofs] at hrun
  obtain ⟨h0, u0, g0, w0⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d0⟩ := pinAt_run (x := ConLeche.natDivName) hp (by rfl) g0
  have b0 := beq_handle_iff hst.wf hn d0
  rcases AM.ite_ok w0 with ⟨y0, a0⟩ | ⟨z0, v0⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a0
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_pos (b0.mp y0)]
    exact hps.divProofs
  have nb0 : ¬ (nm = ConLeche.natDivName) := fun h => z0 (b0.mpr h)
  obtain ⟨h1, u1, g1, w1⟩ := AM.bind_ok v0
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natGcdName) hp (by rfl) g1
  have b1 := beq_handle_iff hst.wf hn d1
  rcases AM.ite_ok w1 with ⟨y1, a1⟩ | ⟨z1, v1⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a1
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_pos (b1.mp y1)]
    exact hps.gcdProofs
  have nb1 : ¬ (nm = ConLeche.natGcdName) := fun h => z1 (b1.mpr h)
  obtain ⟨h2, u2, g2, w2⟩ := AM.bind_ok v1
  obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natLandName) hp (by rfl) g2
  have b2 := beq_handle_iff hst.wf hn d2
  rcases AM.ite_ok w2 with ⟨y2, a2⟩ | ⟨z2, v2⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a2
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_pos (b2.mp y2)]
    exact hps.landProofs
  have nb2 : ¬ (nm = ConLeche.natLandName) := fun h => z2 (b2.mpr h)
  obtain ⟨h3, u3, g3, w3⟩ := AM.bind_ok v2
  obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natLorName) hp (by rfl) g3
  have b3 := beq_handle_iff hst.wf hn d3
  rcases AM.ite_ok w3 with ⟨y3, a3⟩ | ⟨z3, v3⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a3
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_pos (b3.mp y3)]
    exact hps.lorProofs
  have nb3 : ¬ (nm = ConLeche.natLorName) := fun h => z3 (b3.mpr h)
  obtain ⟨h4, u4, g4, w4⟩ := AM.bind_ok v3
  obtain ⟨rfl, d4⟩ := pinAt_run (x := ConLeche.natXorName) hp (by rfl) g4
  have b4 := beq_handle_iff hst.wf hn d4
  rcases AM.ite_ok w4 with ⟨y4, a4⟩ | ⟨z4, v4⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a4
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_pos (b4.mp y4)]
    exact hps.xorProofs
  have nb4 : ¬ (nm = ConLeche.natXorName) := fun h => z4 (b4.mpr h)
  obtain ⟨h5, u5, g5, w5⟩ := AM.bind_ok v4
  obtain ⟨rfl, d5⟩ := pinAt_run (x := ConLeche.natShiftLeftName) hp (by rfl) g5
  have b5 := beq_handle_iff hst.wf hn d5
  rcases AM.ite_ok w5 with ⟨y5, a5⟩ | ⟨z5, v5⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a5
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_pos (b5.mp y5)]
    exact hps.shiftLeftProofs
  have nb5 : ¬ (nm = ConLeche.natShiftLeftName) := fun h => z5 (b5.mpr h)
  obtain ⟨h6, u6, g6, w6⟩ := AM.bind_ok v5
  obtain ⟨rfl, d6⟩ := pinAt_run (x := ConLeche.natShiftRightName) hp (by rfl) g6
  have b6 := beq_handle_iff hst.wf hn d6
  rcases AM.ite_ok w6 with ⟨y6, a6⟩ | ⟨z6, v6⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok a6
    refine ⟨rfl, ?_⟩
    rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_pos (b6.mp y6)]
    exact hps.shiftRightProofs
  have nb6 : ¬ (nm = ConLeche.natShiftRightName) := fun h => z6 (b6.mpr h)
  obtain ⟨rfl, rfl⟩ := AM.pure_ok v6
  refine ⟨rfl, ?_⟩
  rw [ConLeche.divModCertProofs, if_neg nb0, if_neg nb1, if_neg nb2, if_neg nb3, if_neg nb4, if_neg nb5, if_neg nb6]
  exact hps.modProofs

/-- con-leche: ConLeche/Kernel/Checker.lean:292-297 divModPinGuard — one
variant's pin guards.

**PROVED** (task #97-P3-Checker round 10): `divModDeclPin_run` (the
handle-comparison chain against the pins), then `pinGuardWalk_run`, the four
walks `reducePinGuard_run` shares. -/
theorem divModPinGuard_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {r : Bool} {s s' : AState}
    (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm)
    (hr : Arena.divModPinGuard ps fe cn s = .ok (r, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      r = ConLeche.divModPinGuard psP env nm := by
  simp only [Arena.divModPinGuard] at hr
  obtain ⟨p, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨rfl, hpd⟩ := divModDeclPin_run hck.state hck.pins hps hn g1
  simp only [ConLeche.divModPinGuard, Bool.and_assoc]
  exact pinGuardWalk_run hck (Ext.refl _) rfl hpd r1

/-- con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard — one
variant's certificate guards, over the pinned statements.

`sorry`: `divModCertStmts`' exactness (eight branches of `natAp*`/`eqAt1`,
the `natOpEquations_run` generator), `divModCertProofs`' handle chain, a
full-walk `substConstAll_run`, `substConst0List`, and the guard walks. -/
theorem divModCertsGuard_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {val : EIdx} {v : Expr} {r : Bool} {s s' : AState}
    (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm) (hv : denoteE s.store val = some v)
    (hr : Arena.divModCertsGuard ps fe cn val s = .ok (r, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      r = ConLeche.divModCertsGuard psP env nm v := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt — one
variant's attempt: on success the invariant stands, and a `true` answer is
con-leche's.

`sorry`: two `KnotSpec.annotate` and one `KnotSpec.defeq` at depth 0 for the
pin, then the certificate loop — `KnotSpec.annotate`/`infer`/`defeq` at
depth 4 over `divModCertApplied`, whose `WScoped 4` preconditions need a
`natOpEquations_wscoped`-style fact about the pinned statements. -/
theorem checkDivModPinAt_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {ps : INatOpPinSet} {psP : NatOpPinSet} {cn : NIdx} {nm : ConLeche.Name}
    {val : EIdx} {v : Expr} {b : Bool} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (hck : CheckOK μ env fe s) (hps : PinSetDenote s.store ps psP)
    (hn : denoteN s.store.ns cn = some nm) (hv : denoteE s.store val = some v)
    (hwsv : Expr.WScoped 0 v)
    (hr : Arena.checkDivModPinAt μ fe cn val ps s = .ok (b, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      (b = true → ∃ F, ConLeche.checkDivModPinAt (ConLeche.fueledOps μ F) env nm v psP
        = .ok true) := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:338-360 checkDivModPinLoop — **the
variant loop**: an accepting arena loop is an accepting pure loop, at some
fuel, whatever the two sides' decline messages.  PROVED over the four pieces
above (the module section's note says why only their `true` direction is
spent). -/
theorem checkDivModPinLoop_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cn : NIdx} {nm : ConLeche.Name} {val : EIdx} {v : Expr}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (henv : EnvWF env) (hwsv : Expr.WScoped 0 v) :
    ∀ (ps : List INatOpPinSet) (psP : List NatOpPinSet) (tried : List String)
      (triedP : List String) (s s' : AState),
      CheckOK μ env fe s → PinsDenote s.store ps psP →
      denoteN s.store.ns cn = some nm → denoteE s.store val = some v →
      Arena.checkDivModPinLoop μ fe cn val ps tried s = .ok ((), s') →
      CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
        ∃ F, ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v psP triedP
          = .ok () := by
  intro ps
  induction ps with
  | nil =>
    intro psP tried triedP s s' _ _ _ _ hrun
    simp only [Arena.checkDivModPinLoop] at hrun
    exact absurd hrun (AM.Never.bind (fun _ => AM.Never.fail _) s () s')
  | cons p rest ih =>
    intro psP tried triedP s s' hck hps hn hv hrun
    cases psP with
    | nil => exact hps.elim
    | cons q restP =>
    obtain ⟨hq, hrestP⟩ := hps
    simp only [Arena.checkDivModPinLoop] at hrun
    obtain ⟨a, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨hck1, hx1, hp1, rfl⟩ := divModPinGuard_run hck hq hn g1
    have hq1 := (PinsDenote.mono hx1 [p] [q] ⟨hq, trivial⟩).1
    obtain ⟨b, s2, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨hck2, hx2, hp2, rfl⟩ :=
      divModCertsGuard_run hck1 hq1 (denoteN_ext hn hx1) (denote_ext hv hx1) g2
    have hx02 : Ext s.store s2.store := hx1.trans hx2
    have hn2 := denoteN_ext hn hx02
    have hv2 := denote_ext hv hx02
    have hrest2 := PinsDenote.mono hx02 _ _ hrestP
    -- the pure side's step, whichever branch its attempt takes
    have pureStep : ∀ F, (ConLeche.divModPinGuard q env nm &&
        ConLeche.divModCertsGuard q env nm v) = true →
        (ConLeche.checkDivModPinAt (ConLeche.fueledOps μ F) env nm v q = .ok true ∨
          ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v restP
            (triedP ++ [ConLeche.divModAttemptReason q none]) = .ok ()) →
        ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v (q :: restP) triedP
          = .ok () := by
      intro F hg hor
      simp only [ConLeche.checkDivModPinLoop, hg, if_true, fueledOps_orElse]
      split
      · rfl
      · rcases hor with h | h
        · rename_i hne; exact absurd h hne
        · exact h
    -- the rest of the loop, at the state the step left
    have recurse : ∀ (t : AState) (tr : List String), CheckOK μ env fe t →
        Ext s.store t.store → t.pins = s.pins →
        Arena.checkDivModPinLoop μ fe cn val rest tr t = .ok ((), s') →
        CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
          ∃ F, ConLeche.checkDivModPinLoop (ConLeche.fueledOps μ F) env nm v (q :: restP)
            triedP = .ok () := by
      intro t tr hckt hxt hpt hrt
      by_cases hg : (ConLeche.divModPinGuard q env nm &&
          ConLeche.divModCertsGuard q env nm v) = true
      · obtain ⟨hck', hx', hp', F, hF⟩ :=
          ih restP tr (triedP ++ [ConLeche.divModAttemptReason q none]) t s' hckt
            (PinsDenote.mono hxt _ _ hrestP) (denoteN_ext hn hxt) (denote_ext hv hxt) hrt
        exact ⟨hck', hxt.trans hx', by rw [hp', hpt], F, pureStep F hg (Or.inr hF)⟩
      · obtain ⟨hck', hx', hp', F, hF⟩ :=
          ih restP tr (triedP ++ [s!"{q.toolchain}: pin or certificate ground constants \
          absent"]) t s' hckt
            (PinsDenote.mono hxt _ _ hrestP) (denoteN_ext hn hxt) (denote_ext hv hxt) hrt
        refine ⟨hck', hxt.trans hx', by rw [hp', hpt], F, ?_⟩
        rw [Bool.not_eq_true] at hg
        simp only [ConLeche.checkDivModPinLoop, hg, Bool.false_eq_true, if_false]
        exact hF
    have hp02 : s2.pins = s.pins := by rw [hp2, hp1]
    split at r2
    · rename_i hg
      obtain ⟨o, s3, g3, r3⟩ := AM.bind_ok r2
      rcases orElseAttempt_run g3 with ⟨b', ha, ho⟩ | ⟨e, ha, ho, rfl⟩
      · obtain ⟨hck3, hx3, hp3, himp⟩ :=
          checkDivModPinAt_bridge hμ hk henv hck2 (PinsDenote.mono hx2 [p] [q] ⟨hq1, trivial⟩).1
            hn2 hv2 hwsv ha
        cases b' with
        | true =>
          simp only [orElseStepOf] at ho
          subst ho
          obtain ⟨-, rfl⟩ := AM.pure_ok r3
          obtain ⟨F, hF⟩ := himp rfl
          exact ⟨hck3, hx02.trans hx3, by rw [hp3, hp02], F, pureStep F hg (Or.inl hF)⟩
        | false =>
          simp only [orElseStepOf] at ho
          subst ho
          exact recurse s3 _ hck3 (hx02.trans hx3) (by rw [hp3, hp02]) r3
      · cases e <;> (simp only [orElseStepOf] at ho; subst ho)
        all_goals first
          | exact absurd r3 (AM.Never.fail _ _ _ _)
          | exact recurse _ _ hck2 hx02 hp02 r3
    · exact recurse s2 _ hck2 hx02 hp02 r2

/-- con-leche: ConLeche/Kernel/Checker.lean:380-388 checkDivModPin — **the
`Nat.div`/`Nat.mod` variant gate**: the stored value must be definitionally
equal to some committed pin variant and that variant's certificates must
check.  No variant matching is a decline.

**SKELETONISED** (task #97-P3-Checker round 9): the environment guard
(`divModEnvGuard_run`), the lookup of the stored value through the extended
index's `IFEnvOK` (its `WScoped 0` from `EnvWF env2`), and the variant loop
(`checkDivModPinLoop_bridge`, PROVED) — over the four named pieces above:
`divModEnvGuard_run`, `divModPinGuard_run`, `divModCertsGuard_run`,
`checkDivModPinAt_bridge`. -/
theorem checkDivModPin_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env env2 : Env}
    {fe fe2 : IFEnv} {cn : NIdx} {nm : ConLeche.Name} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hok2 : StepOK env2 fe2 s)
    (hpins : PinsDenote s.store pins pinsP)
    (hn : denoteN s.store.ns cn = some nm)
    (hrun : checkDivModPin μ pins fe fe2 cn s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkDivModPin (ConLeche.fueledOps μ F) pinsP env env2 nm
        = .ok () := by
  simp only [Arena.checkDivModPin] at hrun
  obtain ⟨g, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, hx1, hc1, hp1, rfl⟩ :=
    divModEnvGuard_run hok.check.state hok.check.pins hok2.ienv hn g1
  split at r1
  · rename_i hG
    cases hf : fe2.find? cn with
    | none =>
      rw [hf] at r1
      exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | some ci =>
    rw [hf] at r1
    match ci, hf, r1 with
    | .defnInfo cvI value' hint', hfind, r1 =>
      obtain ⟨nm0, c, hn0, hci, hfindP⟩ := hok2.ienv.hit cn _ hfind
      rw [hn] at hn0
      obtain rfl := Option.some.inj hn0
      simp only [Frontend.denoteCI] at hci
      cases hcv : Frontend.denoteCV s.store cvI with
      | none => rw [hcv] at hci; simp at hci
      | some cv' =>
      cases hvv : denoteE s.store value' with
      | none => rw [hcv, hvv] at hci; simp at hci
      | some v' =>
      rw [hcv, hvv] at hci
      simp only [Option.some.injEq] at hci
      subst hci
      have hwc := hok2.envWF _ (List.mem_of_find?_eq_some hfindP)
      obtain ⟨hf1, -, -, -⟩ := hwc.2.2.2.2.1 cv' v' hint' rfl
      have hck1 : CheckOK μ env fe s1 := hok.check.mono hst1 hx1 hc1 hp1
      obtain ⟨hck', hx', hp', F, hF⟩ :=
        checkDivModPinLoop_bridge hμ hk hok.envWF (ConLeche.Expr.WScoped.of_not_hasFvar hf1)
          pins pinsP [] [] s1 s' hck1 (PinsDenote.mono hx1 _ _ hpins) (denoteN_ext hn hx1)
          (denote_ext hvv hx1) r1
      refine ⟨hck'.state, hx1.trans hx', by rw [hp', hp1], F, ?_⟩
      simp only [ConLeche.checkDivModPin, hG, hfindP, if_true]
      exact hF
    | .axiomInfo _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .thmInfo _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .indInfo _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .ctorInfo _ _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .recInfo _ _ _ _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
    | .projInfo _, _, r1 => exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)
  · exact absurd r1 (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

/-! ## The compiler-trust gate's pieces -/

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:202-207 reduceDeclPin — the
pinned defining expression of a reduce operation, interned. -/
theorem reduceDeclPin_run {cH : NIdx} {cn : ConLeche.Name} {p : EIdx}
    {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hd : denoteN s.store.ns cH = some cn)
    (hrun : Arena.reduceDeclPin cH s = .ok (p, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store p = some (ConLeche.reduceDeclPin cn) := by
  simp only [Arena.reduceDeclPin] at hrun
  obtain ⟨rn, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.reduceNatName) hp (by rfl) g1
  have hiff := beq_handle_iff hst.wf hd d1
  rcases AM.ite_ok r1 with ⟨hc, k⟩ | ⟨hc, k⟩
  · obtain ⟨hs, hv⟩ := Frontend.internExpr_sstep hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.reduceDeclPin, if_pos (hiff.mp hc)]
  · obtain ⟨hs, hv⟩ := Frontend.internExpr_sstep hst k
    refine ⟨hs, ?_⟩
    rw [hv, ConLeche.reduceDeclPin, if_neg (fun h => hc (hiff.mpr h))]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:215-218 reduceCertVar — the
identity certificate's variable, `fvar 0` at the element type, interned. -/
theorem reduceCertVar_run {cH : NIdx} {cn : ConLeche.Name} {v : EIdx}
    {s s' : AState} (hst : StateOK s) (hp : PinsOK s)
    (hd : denoteN s.store.ns cH = some cn)
    (hrun : Arena.reduceCertVar cH s = .ok (v, s')) :
    Frontend.IStepS s s' ∧ denoteE s'.store v = some (ConLeche.reduceCertVar cn) := by
  simp only [Arena.reduceCertVar, Arena.reduceElemTy, Arena.reduceElemName]
    at hrun
  obtain ⟨ty, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨nm, s0, g0, r0⟩ := AM.bind_ok g1
  obtain ⟨rn, s00, g00, r00⟩ := AM.bind_ok g0
  obtain ⟨p00, d1⟩ := pinAt_run (x := ConLeche.reduceNatName) hp (by rfl) g00
  rw [p00] at r00
  have hiff := beq_handle_iff hst.wf hd d1
  have hname : denoteN s.store.ns nm = some (ConLeche.reduceElemName cn) ∧ s0 = s := by
    rcases AM.ite_ok r00 with ⟨hc, k⟩ | ⟨hc, k⟩
    · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natName) hp (by rfl) k
      refine ⟨?_, rfl⟩
      rw [d2, ConLeche.reduceElemName, if_pos (hiff.mp hc)]
    · obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.boolName) hp (by rfl) k
      refine ⟨?_, rfl⟩
      rw [d2, ConLeche.reduceElemName, if_neg (fun h => hc (hiff.mpr h))]
  obtain ⟨hnm, rfl⟩ := hname
  obtain ⟨hs1, hty⟩ := constE_run hst hp hnm r0
  obtain ⟨hs2, hv⟩ := Frontend.internE_sstep hs1.ok
    (viewOK_fvar (by rw [hty]; rfl)) r1
  refine ⟨hs1.trans hs2, ?_⟩
  rw [hv]
  simp only [denoteEView, denote_ext hty hs2.ext, Option.map_some]
  have : ConLeche.reduceElemTy cn = .const (ConLeche.reduceElemName cn) [] := by
    unfold ConLeche.reduceElemTy ConLeche.reduceElemName
    split <;> rfl
  rw [ConLeche.reduceCertVar, this]

/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:209-213 reducePinGuard — the
pin's syntactic guards are con-leche's.  `reduceDeclPin_run`, then
`pinGuardWalk_run`. -/
theorem reducePinGuard_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cH : NIdx} {cn : ConLeche.Name} {r : Bool} {s s' : AState}
    (hck : CheckOK μ env fe s) (hd : denoteN s.store.ns cH = some cn)
    (hrun : Arena.reducePinGuard fe cH s = .ok (r, s')) :
    CheckOK μ env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      r = ConLeche.reducePinGuard env cn := by
  simp only [Arena.reducePinGuard] at hrun
  obtain ⟨p, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hpd⟩ := reduceDeclPin_run hck.state hck.pins hd g1
  have hck1 : CheckOK μ env fe s1 :=
    hck.mono hs1.ok hs1.ext hs1.caches hs1.pins
  simp only [ConLeche.reducePinGuard, Bool.and_assoc]
  exact pinGuardWalk_run hck1 hs1.ext hs1.pins hpd r1

/-- con-leche: ConLeche/Kernel/Checker.lean:407-425 checkReducePin — the pure
side of an accepted gate, at ONE fuel. -/
theorem checkReducePin_pure {μ : CheckMode} {env env2 : Env} {F : Nat}
    {nm : ConLeche.Name} {x w pw : Expr}
    (h1 : (ConLeche.reduceStoredOk env2 nm && ConLeche.reduceElemOk env nm) = true)
    (h2 : ConLeche.reducePinGuard env nm = true)
    (h3 : ConLeche.annotateCore μ env F 0 x = .ok w)
    (h4 : ConLeche.annotateCore μ env F 0 (ConLeche.reduceDeclPin nm) = .ok pw)
    (h5 : ConLeche.isDefEqCore μ env F 0 w pw = .ok true)
    (h6 : ConLeche.isDefEqCore μ env F 1 (.app w (ConLeche.reduceCertVar nm))
      (ConLeche.reduceCertVar nm) = .ok true) :
    ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x = .ok () := by
  simp only [ConLeche.checkReducePin, ConLeche.fueledOps, h1, h2, h3, h4, h5, h6,
    if_true, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Checker.lean:93-110 checkOpaqueVal — an
accepted opaque's raw value has no free variable (the second guard). -/
theorem checkOpaqueVal_noFvar {μ : CheckMode} {env env' : Env} {F : Nat}
    {c : ConstantVal} {x : Expr}
    (h : ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env') :
    x.hasFvar = false := by
  cases hb : x.hasFvar with
  | false => rfl
  | true =>
    exfalso
    simp only [ConLeche.checkOpaqueVal, hb] at h
    cases hl : x.looseBVarsBounded 0 <;>
      simp [hl, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

/-- con-leche: ConLeche/Kernel/Checker.lean:407-425 checkReducePin — the
`Lean.reduceNat` / `Lean.reduceBool` install gate: the stored value must be
definitionally equal to the build-time pin.

`sorry`: `reduceStoredOk` / `reduceElemOk` / `reducePinGuard` through
`IFEnvOK`, then `KnotSpec.annotate` and `KnotSpec.defeq` at the
pinned term.  Task #97-P3-Checker's sorry list, item 24. -/
theorem checkReducePin_bridge {μ : CheckMode} {env env2 : Env}
    {fe fe2 : IFEnv} {cn : NIdx} {nm : ConLeche.Name} {value : EIdx}
    {x : Expr} {s s' : AState} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (hok : FoldOK μ env fe s)
    (hok2 : StepOK env2 fe2 s)
    (hn : denoteN s.store.ns cn = some nm)
    (hv : denoteE s.store value = some x) (hws : Expr.WScoped 0 x)
    (hrun : checkReducePin μ fe fe2 cn value s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x
        = .ok () := by
  have hknot := hk.knot env fe hok.envWF
  have hck := hok.check
  simp only [Arena.checkReducePin] at hrun
  obtain ⟨b1, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, rfl⟩ := reduceStoredOk_run hck.state hck.pins hok2.ienv hn _ _ g1
  obtain ⟨b2, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hs2, rfl⟩ := reduceElemOk_run hs1.ok (hck.pins.mono hs1.ext hs1.pins)
    (hck.ienv.mono hs1.ext) (denoteN_ext hn hs1.ext) _ _ g2
  have hs12 := hs1.trans hs2
  have hck2 : CheckOK μ env fe s2 :=
    hck.mono hs12.ok hs12.ext hs12.caches hs12.pins
  rcases AM.ite_ok r2 with ⟨hc1, r3⟩ | ⟨-, r3⟩
  rotate_left
  · exact absurd r3 AM.readFail_ne
  obtain ⟨b3, s3, g3, r4⟩ := AM.bind_ok r3
  obtain ⟨hck3, hx3, hp3, rfl⟩ :=
    reducePinGuard_run hck2 (denoteN_ext hn hs12.ext) g3
  rcases AM.ite_ok r4 with ⟨hc2, r5⟩ | ⟨-, r5⟩
  rotate_left
  · exact absurd r5 AM.readFail_ne
  have hx03 : Ext s.store s3.store := hs12.ext.trans hx3
  -- the value, annotated
  obtain ⟨va, s4, g4, r6⟩ := AM.bind_ok r5
  obtain ⟨hck4, hx4, hp4, hsim4⟩ := AM.of_run (P := fun t => t = s3)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s3.store t.store ∧
      t.pins = s3.pins ∧ Core.SimE (ConLeche.annotateCore μ env) 0 x t.store r)
    rfl g4 (hknot.annotate s3 0 value x hck3 (denote_ext hv hx03) hws)
  obtain ⟨w, hw4, hwsw, F4, hF4⟩ := hsim4
  have hx04 : Ext s.store s4.store := hx03.trans hx4
  -- the pin, interned again and annotated
  obtain ⟨p, s5, g5, r7⟩ := AM.bind_ok r6
  obtain ⟨hs5, hpd⟩ := reduceDeclPin_run hck4.state hck4.pins
    (denoteN_ext hn hx04) g5
  have hck5 : CheckOK μ env fe s5 := hck4.mono hs5.ok hs5.ext hs5.caches hs5.pins
  have hwsP : Expr.WScoped 0 (ConLeche.reduceDeclPin nm) := by
    refine ConLeche.Expr.WScoped.of_not_hasFvar ?_
    simp only [ConLeche.reducePinGuard, Bool.and_eq_true, Bool.not_eq_true'] at hc2
    exact hc2.1.1.2
  obtain ⟨pa, s6, g6, r8⟩ := AM.bind_ok r7
  obtain ⟨hck6, hx6, hp6, hsim6⟩ := AM.of_run (P := fun t => t = s5)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s5.store t.store ∧
      t.pins = s5.pins ∧
      Core.SimE (ConLeche.annotateCore μ env) 0 (ConLeche.reduceDeclPin nm) t.store r)
    rfl g6 (hknot.annotate s5 0 p _ hck5 hpd hwsP)
  obtain ⟨pw, hpw6, hwspw, F6, hF6⟩ := hsim6
  have hx56 : Ext s4.store s6.store := hs5.ext.trans hx6
  -- the pin comparison
  obtain ⟨ok1, s7, g7, r9⟩ := AM.bind_ok r8
  obtain ⟨hck7, hx7, hp7, hsim7⟩ := AM.of_run (P := fun t => t = s6)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s6.store t.store ∧
      t.pins = s6.pins ∧ Core.SimV (ConLeche.isDefEqCore μ env) 0 w pw r)
    rfl g7 (hknot.defeq s6 0 va pa w pw hck6 (denote_ext hw4 hx56) hpw6 hwsw hwspw)
  obtain ⟨F7, hF7⟩ := hsim7
  rcases AM.ite_ok r9 with ⟨hc7, r10⟩ | ⟨-, r10⟩
  rotate_left
  · exact absurd r10 AM.readFail_ne
  have hc7' : ok1 = true := hc7
  subst hc7'
  -- the identity certificate
  have hx47 : Ext s4.store s7.store := hx56.trans hx7
  obtain ⟨xv, s8, g8, r11⟩ := AM.bind_ok r10
  obtain ⟨hs8, hxv⟩ := reduceCertVar_run hck7.state hck7.pins
    (denoteN_ext hn (hx04.trans hx47)) g8
  have hck8 : CheckOK μ env fe s8 := hck7.mono hs8.ok hs8.ext hs8.caches hs8.pins
  have hw8 : denoteE s8.store va = some w := denote_ext hw4 (hx47.trans hs8.ext)
  obtain ⟨ax, s9, g9, r12⟩ := AM.bind_ok r11
  obtain ⟨hs9, hax⟩ := Frontend.internE_sstep hck8.state
    (viewOK_app (by rw [hw8]; rfl) (by rw [hxv]; rfl)) g9
  have hax' : denoteE s9.store ax
      = some (.app w (ConLeche.reduceCertVar nm)) := by
    rw [hax]
    simp only [denoteEView, denote_ext hw8 hs9.ext, denote_ext hxv hs9.ext, opt2]
  have hck9 : CheckOK μ env fe s9 := hck8.mono hs9.ok hs9.ext hs9.caches hs9.pins
  have hwsC : Expr.WScoped 1 (ConLeche.reduceCertVar nm) := by
    unfold ConLeche.reduceCertVar ConLeche.reduceElemTy
    split <;> simp [Expr.WScoped]
  have hwsA : Expr.WScoped 1 (.app w (ConLeche.reduceCertVar nm)) := by
    unfold Expr.WScoped
    exact ⟨ConLeche.Expr.WScoped.mono (by omega) hwsw, hwsC⟩
  obtain ⟨ok2, s10, g10, r13⟩ := AM.bind_ok r12
  obtain ⟨hck10, hx10, hp10, hsim10⟩ := AM.of_run (P := fun t => t = s9)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s9.store t.store ∧
      t.pins = s9.pins ∧
      Core.SimV (ConLeche.isDefEqCore μ env) 1 (.app w (ConLeche.reduceCertVar nm))
        (ConLeche.reduceCertVar nm) r)
    rfl g10 (hknot.defeq s9 1 ax xv _ _ hck9 hax' (denote_ext hxv hs9.ext)
      hwsA hwsC)
  obtain ⟨F10, hF10⟩ := hsim10
  rcases AM.ite_ok r13 with ⟨hc10, r14⟩ | ⟨-, r14⟩
  rotate_left
  · exact absurd r14 AM.readFail_ne
  have hc10' : ok2 = true := hc10
  subst hc10'
  obtain ⟨-, rfl⟩ := AM.pure_ok r14
  refine ⟨hck10.state,
    (((hx04.trans hx56).trans hx7).trans (hs8.ext.trans hs9.ext)).trans hx10,
    by rw [hp10, hs9.pins, hs8.pins, hp7, hp6, hs5.pins, hp4, hp3, hs12.pins],
    max (max F4 F6) (max F7 F10), ?_⟩
  have l4 : F4 ≤ max (max F4 F6) (max F7 F10) := by omega
  have l6 : F6 ≤ max (max F4 F6) (max F7 F10) := by omega
  have l7 : F7 ≤ max (max F4 F6) (max F7 F10) := by omega
  have l10 : F10 ≤ max (max F4 F6) (max F7 F10) := by omega
  exact checkReducePin_pure hc1 hc2 (ConLeche.annotateCore_mono l4 hF4)
    (ConLeche.annotateCore_mono l6 hF6) (ConLeche.isDefEqCore_mono l7 hF7)
    (ConLeche.isDefEqCore_mono l10 hF10)

end ConRon.Bridge
