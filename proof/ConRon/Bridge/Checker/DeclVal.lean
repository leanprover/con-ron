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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpGuard) — the
structural-`Nat` environment guard is con-leche's at the denoted environment.

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4 — the same
defect as `natOpDeps_run`'s above, found by the grep that round asks for):
`natOpGuard` reads eight pins (`natLitSupported`'s three, `natBeqName`,
`natBleName`, `natDivModNames`, `boolTrueName`, `boolFalseName`) and asked
only for `StateOK`, so nothing made the handles `pinAt` hands back denote
anything and the conclusion was not provable.  Free at the one call site
(`Bridge/Checker/Arms.lean`'s `defn` arm, `hok4.check.pins`).

`sorry`: `natLitSupported` / `natOpDepsStored` / the `Bool`-family lookups
through `IFEnvOK`, then `natOpDeps_run`.  Task #97-P3-Checker's sorry list,
item 23. -/
theorem natOpGuard_run {env2 : Env} {fe2 : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpGuard fe2 cn s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.natOpGuard env2 nm := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpStoredOk) — the twin's list
recursion answers con-leche's `List.all` (DESIGN §3.4 forbids the closure).

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4): each step
is `natOpStoredOk`, which is `natOpTyPinned` on a hit, which reads the pin
table — so this walk is a pin reader too and `StateOK` alone was not enough.
Free at the one call site (`hok5.check.pins`).

`sorry`: a list induction over `natOpStoredOk`'s own `IFEnvOK` reads.  Task
#97-P3-Checker's sorry list, item 23. -/
theorem natOpStoredOkAll_run {env2 : Env} {fe2 : IFEnv} {ds : List NIdx}
    {xs : List ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s)
    (hie : IFEnvOK env2 fe2 s) (hd : denoteNL s.store ds xs)
    (hr : natOpStoredOkAll fe2 ds s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = xs.all (ConLeche.natOpStoredOk env2) := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpEquations) — the recurrence
equations, interned.

`sorry`: the pinned-literal constructions through the frontend tier's intern
exactness, as `Bridge/Checker/Basis.lean`'s item 15.  Task #97-P3-Checker's
sorry list, item 23. -/
theorem natOpEquations_run {d : Nat} {cn : NIdx} {nm : ConLeche.Name}
    {eqs : List (EIdx × EIdx)} {s s' : AState} (hok : StateOK s)
    (hp : PinsOK s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpEquations d cn s = .ok (eqs, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      EqPairsDenote s'.store eqs (ConLeche.natOpEquations d nm) := by
  sorry

/-- con-leche: ConLeche/Kernel/ExprOps.lean (Expr.substConst0) — the
self-reference substitution, pair by pair.

**The statement gained `PinsOK s`** (task #97-P3-Checker round 4):
`substConst0`'s `.const` arm reads `emptyLevels` and compares the stored
universe-argument handle against it, so without the pin invariant nothing
ties that comparison to con-leche's `us = []`.  Free at the one call site
(`hok7.check.pins`).

`sorry`: a list recursion over `Bridge/ExprOps/**`'s `substConst0` spec.  Task
#97-P3-Checker's sorry list, item 23. -/
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
  sorry



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

/-- con-leche: ConLeche/Kernel/Checker.lean:110-125 certifyNatEqs — the
substituted recurrence equations are well scoped at the depth the certifier
runs them at (`isDefEq … 2`: the equations' variables are `fvar 0` and
`fvar 1`).  A pure fact about con-leche's own pinned construction, which
`certifyNatEqs_bridge`'s `KnotSpec.defeq` calls need as their precondition.

`sorry`: `natOpEquations`' twelve literal shapes, and `Expr.substConst0`
preserving `WScoped` at a well-scoped replacement — which the stored value is,
by `EnvWF env2`'s own clause about a `defnInfo`'s value.  Task
#97-P3-Checker's sorry list, item 23. -/
theorem natOpEqs_wscoped {env2 : Env} {nm : ConLeche.Name}
    {cv' : ConstantVal} {v' : Expr} {hint' : ReducibilityHint}
    (henv : EnvWF env2)
    (hf : env2.find? nm = some (.defnInfo cv' v' hint')) :
    ∀ q ∈ (ConLeche.natOpEquations 0 nm).map
      (fun eq => (Expr.substConst0 nm v' eq.1, Expr.substConst0 nm v' eq.2)),
      Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2 := by
  sorry

/-! ## The two pinned-variant gates -/

/-- con-leche: ConLeche/Kernel/Checker.lean:380-388 checkDivModPin — **the
`Nat.div`/`Nat.mod` variant gate**: the stored value must be definitionally
equal to some committed pin variant and that variant's certificates must
check.  No variant matching is a decline.

The loop is the one consumer of `Bridge/Checker/Base.lean`'s
`orElseAttempt_run`: each variant is an ATTEMPT, and a thrown error inside one
is "this variant does not match", recovered at the pre-attempt state.

`sorry`: `orElseAttempt_run` at each variant, `PinsDenote` to line the
variants up with con-leche's, `divModCertStmts`' pinned-term exactness, and
`KnotSpec.defeq` / `KnotSpec.infer` for the certificates.  Task
#97-P3-Checker's sorry list, item 24. -/
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
  sorry

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
    (hv : denoteE s.store value = some x)
    (hrun : checkReducePin μ fe fe2 cn value s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x
        = .ok () := by
  sorry

end ConRon.Bridge
