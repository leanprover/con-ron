/-
# `ConRon.Bridge.Checker.Split` — the two folds are one accept

`Arena/Checker.lean` has two folds and its module note says why:

> * **`checkDeclsPure`** is the THEOREM's shape […] one step per record,
>   install and check together.
> * **`installThenCheck`** is what the BINARY runs […] phase A installs every
>   record, annotating its header and its value but not inferring; phase B
>   checks each recorded declaration against the PREFIX VIEW it was installed
>   at.  con-leche proves the two are the same accept
>   (`fullyChecked_checkDecls`).

`Bridge/Checker/Fold.lean` proves Theorem 1 for `checkDeclsPure`.  This module
is what carries it to `installThenCheck`, and it is the history report's
**fine print 5** in full:

> If the foreign core wants the two-phase install-then-check fold rather than
> `checkDeclsPure`'s straight fold, it must additionally re-derive
> `checkDecl_of_split_{defn,thm,opaque}` (`Verify/CheckerSplit.lean`) and the
> prefix-view congruence (`KnotCongr.lean:543`,
> `mkFEnv_find?_visibleBelow`).

Both exist in con-leche at `78ded4b6` and neither has to be re-derived — they
have to be *reached*:

* `ConLeche.checkDecl_of_split_defn` / `_thm` / `_opaque`
  (`Verify/CheckerSplit.lean:319` / `:344` / `:364`) take the install half and
  the check half AT THE SAME ENVIRONMENT and give `checkDecl`'s own run.  So
  the arena's phase A must give con-leche's `installConstantVal` /
  `installValue` at the prefix environment, and its phase B must give
  con-leche's `checkValueGroup` at the SAME one;
* `ConLeche.mkFEnv_find?_visibleBelow` (`Verify/EnvBound.lean:141`) is what
  makes "the same one" true: phase B runs at `fe.restrictTo pc.vis`, whose
  `find?` is `(env.prefixTo pc.vis).find?` — the environment the record was
  installed at — provided the final environment's names are `Nodup`.  That
  side condition is `checkConstantVal`'s duplicate test, accumulated over the
  fold.

## The three-way fuel

`checkDecl_of_split_*` take the two halves at ONE fuel and con-leche raises
each half with `installConstantVal_mono` / `checkValueGroup_mono`
(`Verify/CheckerSplit.lean:233`–`:247`) before combining — `max F₁ F` at
`Verify/Cached/InstalledC.lean:416`.  `Bridge/Checker/Mono.lean`'s
`checkDecl_mono` is the same idea one level up, and the fold here needs both.

## What this module states and what it does not

It states the five bridge theorems of `Arena/CheckerSplit.lean` and
`Arena/Checker.lean`'s phase-A/phase-B pair, and the punchline
`Arena.installThenCheck_bridge`.  It does not restate the model tier: the
punchline lands on `Bridge/Checker/Fold.lean`'s `checkDeclsPure` statement, so
`Bridge/Checker/Capstone.lean` covers both folds with one composition.
-/
import ConRon.Bridge.Checker.Fold
import ConLeche.Verify.EnvBound

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The install half -/

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:64-85 installConstantVal —
the header's guards and annotation, without the inference.

`sorry`: the same six guards as `checkConstantVal_bridge`
(`Bridge/Checker/Base.lean`) minus the last two calls; in fact the two share a
proof and this one is the shorter half.  Task #97-P3-Checker's sorry list,
item 17. -/
theorem installConstantVal_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {cv cvA : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : installConstantVal μ fe cv s = .ok (cvA, s')) :
    CoreStep μ env fe s s' ∧ ∃ cA F, Frontend.denoteCV s'.store cvA = some cA ∧
      ConLeche.installConstantVal (ConLeche.fueledOps μ F) env c = .ok cA := by
  sorry

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:87-100 installValue — the
value's guards and annotation.

`sorry`: `looseBVarsBoundedFast` / `hasFvarFast` (`Bridge/ExprOps/Walks.lean`),
`KnotSpec.annotate`, `allLevelParamsDefined_run`,
`constsResolveFFast_run`.  Task #97-P3-Checker's sorry list, item 17. -/
theorem installValue_bridge {μ : CheckMode} {env : Env} {fe : IFEnv}
    {cv : IConstantVal} {c : ConstantVal} {value jv : EIdx} {x : Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : installValue μ fe cv value s = .ok (jv, s')) :
    CoreStep μ env fe s s' ∧ ∃ y F, denoteE s'.store jv = some y ∧
      ConLeche.installValue (ConLeche.fueledOps μ F) env c x = .ok y := by
  sorry

/-! ## The check half -/

/-- con-leche: ConLeche/Kernel/CheckerSplit.lean:102-119 checkValueGroup —
**the check half of a value declaration**, at the environment the constant was
installed at.

`sorry`: `KnotSpec.infer`, `EnsureSortSpec.ensureSort`, the level
comparison (`lvlEq?` through `CacheOK.lvlEq`), `installValue_bridge` for a
theorem's own value, and `KnotSpec.defeq`.  Task #97-P3-Checker's sorry
list, item 17. -/
theorem checkValueGroup_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {g : Arena.ValueGroup} {gP : ConLeche.ValueGroup}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s)
    (hkind : g.kind = .defn ∧ gP.kind = .defn ∨ g.kind = .thm ∧ gP.kind = .thm ∨
      g.kind = .opaque ∧ gP.kind = .opaque)
    (hcv : Frontend.denoteCV s.store g.cvA = some gP.cvA)
    (hjv : denoteE s.store g.jv = some gP.jv)
    (hrun : checkValueGroup μ fe g s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) env gP = .ok () := by
  sorry

/-! ## The prefix view

con-leche's `mkFEnv_find?_visibleBelow` at the arena's `IFEnv.restrictTo`.
This is the one place the environment INDEX is consulted at something other
than the environment it indexes, and it is why `FoldOK` carries `IFEnvCoh`. -/

/-- con-leche: ConLeche/Verify/EnvBound.lean:141 mkFEnv_find?_visibleBelow —
**the prefix view denotes the prefix environment**.  Phase B checks a pending
record against `fe.restrictTo pc.vis`, and this says that view is the
environment the record was installed at.

The `Nodup` side condition is con-leche's own and it is the accumulated
duplicate test of `checkConstantVal`; the fold carries it.

`sorry`: `IFEnvCoh` reduces the left side to `((mkIFEnv fe.env).restrictTo
k).find?`, which `mkFEnv_find?_visibleBelow` computes, and the denotation of
`fe.env.consts.drop (len - k)` is `env.prefixTo k`.  Task #97-P3-Checker's
sorry list, item 18. -/
theorem denoteFEnv_restrictTo {μ : CheckMode} {env : Env} {fe : IFEnv}
    {s : AState} {k : Nat} (hok : FoldOK μ env fe s)
    (hnd : (env.consts.map (·.name)).Nodup) (hk : k ≤ fe.visibleBelow) :
    ∃ envK, denoteFEnv s.store (fe.restrictTo k) = some envK ∧
      envK.find? = (env.prefixTo k).find? := by
  sorry

/-! ## Phase A and phase B -/

/-- con-leche: ConLeche/Cached/Installed.lean:144-183 annotStepC — **phase
A's step, bracketed**: the four arms, the promotion of what leaves the step,
and the drop.

The conclusion is the install half's, not `checkDecl`'s: a value kind leaves a
`PendingCheck` behind and con-leche's `installConstantVal` / `installValue`
is what ran.  The three non-value arms fall through to `checkDecl` and the
conclusion is `Bridge/Checker/Decl.lean`'s `DeclOut`.

`sorry`: `annotStepGo`'s four arms over `installConstantVal_bridge`,
`installValue_bridge` and `Arena.checkDecl_bridge`, then the bracket —
`promoteVG_spec` and `promoteNew_spec` at ONE memo, then `PExt.dropScratch`.
The bracket is `Arena.checkDeclStep_bridge`'s with one operation more.  Task
#97-P3-Checker's sorry list, item 19. -/
theorem Arena.annotStep_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {i : Nat} {fe fe' : IFEnv} {pend pend' : Array PendingCheck}
    {pd : IDeclaration} {d : Declaration} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hpp : PersPinSets pins) (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : Arena.annotStep μ pins i fe pend pd s = .ok ((fe', pend'), s')) :
    ∃ env', FoldOK μ env' fe' s' ∧ PExt s.store s'.store ∧
      Pushed fe fe' ∧ (∀ pc ∈ pend'.toList, PersVG pc.vg) ∧
      (pend'.toList = pend.toList ∨
        ∃ pc, pend'.toList = pend.toList ++ [pc] ∧ pc.pos = i ∧
          pc.vis = fe.visibleBelow) := by
  sorry

/-- con-leche: ConLeche/Cached/Installed.lean:260-274 checkPending — **phase
B's check of one record**, against the prefix view, inside its own bracket.

`sorry`: `denoteFEnv_restrictTo` and `checkValueGroup_bridge`, then the
bracket with nothing to promote (`Arena/Checker.lean`: "Nothing crosses back,
so there is nothing to promote").  Task #97-P3-Checker's sorry list,
item 19. -/
theorem Arena.checkPending_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {pc : PendingCheck} {gP : ConLeche.ValueGroup} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpers : PersVG pc.vg)
    (hnd : (env.consts.map (·.name)).Nodup)
    (hcv : Frontend.denoteCV s.store pc.vg.cvA = some gP.cvA)
    (hjv : denoteE s.store pc.vg.jv = some gP.jv)
    (hrun : Arena.checkPending μ fe pc s = .ok ((), s')) :
    ∃ envK F, FoldOK μ env fe s' ∧ PExt s.store s'.store ∧
      envK.find? = (env.prefixTo pc.vis).find? ∧
      ConLeche.checkValueGroup (ConLeche.fueledOps μ F) envK gP = .ok () := by
  sorry

/-! ## The punchline -/

/-- con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
con-leche: ConLeche/Verify/CheckerSplit.lean:319-380 checkDecl_of_split_*
**THE TWO FOLDS ARE ONE ACCEPT**: what the binary runs implies what the
theorem is about.  With `Bridge/Checker/Fold.lean`'s
`Arena.checkDeclsPure_bridge` this is the second half of DESIGN §8.2's
Theorem 1 — the half the history report's fine print 5 prices — and with
`Bridge/Checker/Capstone.lean` it carries the model to the binary's own fold.

`sorry`: the `InstallRun` induction (con-leche's
`Verify/Cached/InstalledC.lean:456 installRun_model` is the same walk at the
model instead of at `checkDeclsPure`): phase A's records give the install
halves at each prefix environment, `Arena.checkPending_bridge` gives the check
half at the SAME one through `denoteFEnv_restrictTo`, `checkDecl_of_split_*`
combines them into `ConLeche.checkDecl`, and `checkDecl_mono` raises the fuels
to one.  Task #97-P3-Checker's sorry list, item 20 — the largest remaining
item after the seven arms, and the only one that is a *fold* rather than a
*step*. -/
theorem Arena.installThenCheck_bridge {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : Array IDeclaration} {dsP : List Declaration} {fe' : IFEnv}
    {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds.toList, PersDecl x)
    (hden : denoteDecls s.store ds.toList = some dsP)
    (hrun : Arena.installThenCheck μ pins ds s = .ok (.ok fe', s')) :
    ∃ env' F', denoteFEnv s'.store fe' = some env' ∧
      ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F') pinsP dsP
        = .ok env' := by
  sorry

end ConRon.Bridge
