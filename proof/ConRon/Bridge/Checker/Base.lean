/-
# `ConRon.Bridge.Checker.Base` — `CheckerBase`'s specs

The twin of `ConLeche/Kernel/CheckerBase.lean` is `Arena/CheckerBase.lean`,
and this module is its bridge tier: the variant fallback, the two memoised
DAG walks the declaration front door runs, the per-declaration constant check
and the three list checks.

## `orElseAttempt` — the only recovery, and the only thing here that is CLOSED

`Arena/CheckerBase.lean`'s `orElseAttempt` is the one place (B) recovers from
a thrown error, and the module note there records the one seam where (B) and
(C) are not the same state:

> The port keeps its `&mut AState` across a failing attempt, so it restores
> the memos and the caches and KEEPS the store […].  A throw in `StateT σ
> (Except ε)` carries no state at all, so the twin's error arm can only resume
> at `s`, whose store is the pre-attempt one.

`orElseAttempt_run` below is that, as a theorem: the attempt's outcome
determines the step, and on a recovered error the state is *literally* the
pre-attempt one — `attemptRestore s (attemptSnapshot s) = s` is `rfl`, which
is what makes the snapshot/restore pair invisible to the bridge.  con-leche's
`orElse` combinator (`CheckerBase.lean:25-53`'s sixth field, its
`fueledOps` clause) has the same three-way outcome with the same states, so
the two agree on the verdict and on everything the bridge can observe.

**Where con-leche has no counterpart**: `OrElseStep.failed`, the fourth arm,
carries only a `native` error (DESIGN §8.3's ruling), and a `native` claims
nothing.  So the bridge says nothing about that arm and does not need to.

## The rest, and why it is stated rather than proved

Everything else here bottoms out in `KnotSpec` (the annotation and the
inference calls) and in the `ExprOps` tier's walks, and the guards that do
NOT are the memoised ones — `allLevelParamsDefined` and `constsResolveFFast`
— which `Arena/CheckerBase.lean` carries because con-leche's own tree walks do
not terminate on a shared DAG (con-leche's task #210 Part B).  Each is a
memoised walk with an explicitly threaded table, so each needs its own memo
invariant and its own fuel induction, in `Bridge/ExprOps/Walks.lean`'s shape.
That is a tier of its own and this round states it.
-/
import ConRon.Bridge.Checker.Hyp

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The variant fallback -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:25-53 CheckerOps (the `orElse`
field) — **the attempt's snapshot and restore, closed.**  Three outcomes, and
on the recovered one the state handed back is the pre-attempt state itself.

The `rfl` in the last arm is the whole content of the snapshot/restore pair:
`attemptRestore s (attemptSnapshot s)` is `{ s with memos := s.memos,
caches := s.caches }`, which is `s`.  In (C) it is not — the port keeps the
attempt's appended nodes — and `Arena/CheckerBase.lean`'s module note prices
that deviation (`Ext` rather than store equality, eight attempts on the whole
of `Init`). -/
theorem orElseAttempt_run {att : AM Bool} {s s' : AState} {r : OrElseStep}
    (h : orElseAttempt att s = .ok (r, s')) :
    (∃ b, att s = .ok (b, s') ∧ r = orElseStepOf (.ok b)) ∨
      (∃ e, att s = .error e ∧ r = orElseStepOf (.error e) ∧ s' = s) := by
  simp only [orElseAttempt] at h
  revert h
  cases ha : att s with
  | ok p =>
    obtain ⟨b, s₁⟩ := p
    intro h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨b, rfl, rfl⟩
  | error e =>
    intro h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨e, rfl, rfl, rfl⟩

/-- con-leche: none — a `matched` attempt matched, and a `continued` attempt
did not: the step's tag reads back the attempt's `Bool`.  The gate's loop
(`Arena/DeclCheck.lean`'s `checkDivModPinLoop`) dispatches on the tag, so this
is what lets the bridge read the loop. -/
theorem orElseStepOf_ok_iff {b : Bool} :
    orElseStepOf (.ok b) = .matched ↔ b = true := by
  cases b <;> simp [orElseStepOf]

/-! ## The memoised DAG walks of the front door -/

/-- con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
— the memo invariant of `allLevelParamsDefinedGo`: a recorded answer is the
real one.  `Bridge/StateOK.lean`'s `MemoVOK` shape at an explicitly threaded
table (the walk does not use `Monad.lean`'s `Memos`: its answer depends on the
parameter LIST, which is a per-call datum). -/
def LPDMemoOK (params : List ConLeche.Name) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ k v, tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ v = Expr.allLevelParamsDefined params e

/-- con-leche: ConLeche/Kernel/Level.lean:405-407
Expr.allLevelParamsDefinedFast — **Theorem 1 for the front door's
level-parameter guard**: the memoised DAG walk answers what con-leche's
`allLevelParamsDefined` answers at the denoted parameter list.

`sorry`: the fuel induction in `Bridge/ExprOps/Walks.lean`'s shape, with
`LPDMemoOK` threaded (the walk's `memo` is an explicit argument-and-result
pair, so the invariant is a hypothesis and a conclusion rather than a state
clause).  Task #97-P3-Checker's sorry list, item 9. -/
theorem allLevelParamsDefined_run {lps : List NIdx} {ks : List ConLeche.Name}
    {e : EIdx} {x : Expr} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hlps : Frontend.denoteNList s.store.ns lps = some ks)
    (hd : denoteE s.store e = some x)
    (hrun : allLevelParamsDefined lps e s = .ok (r, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      r = Expr.allLevelParamsDefined ks x := by
  sorry

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
— **Theorem 1 for the front door's unresolved-constant guard**: the memoised
DAG walk answers what con-leche's `Expr.constsResolve` answers at the denoted
environment.

`sorry`: the fuel induction, with the memo invariant and `IFEnvOK`'s `hit` /
`miss` pair at the `.const` and `.proj` arms (the walk asks `fe.find?` and
con-leche asks `env.find?`, and `IFEnvOK.miss` — hence `denoteN_inj` — is what
makes the two agree on a MISS).  Task #97-P3-Checker's sorry list, item 9. -/
theorem constsResolveFFast_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {e : EIdx} {x : Expr} {r : Bool} {s s' : AState}
    (hok : FoldOK μ env fe s) (hd : denoteE s.store e = some x)
    (hrun : constsResolveFFast fe e s = .ok (r, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      r = Expr.constsResolve env x := by
  sorry

/-! ## The name-shape guards

Three pure tests on handles.  Each is a handle comparison where con-leche has
a `Name` comparison, and each is exact for the same reason: `denoteN` is
injective (`Arena/WFProofs.lean`'s `denoteN_inj`, DESIGN §8.3's soundness
obligation). -/

/-- con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup — the handle test
is the name test.

`sorry`: a list induction over `denoteN_inj`.  Task #97-P3-Checker's sorry
list, item 10. -/
theorem nameNodup_spec {st : EStore} (hwf : StoreWF st) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns ns = some xs →
        nameNodup ns = ConLeche.Name.nodup xs := by
  sorry

/-- con-leche: ConLeche/Kernel/Level.lean:223-230 Name.isProjFnShape — the
handle test is the name test.

`sorry`: two `viewN` inversions over `denoteN`'s `str`/`num` arms.  Task
#97-P3-Checker's sorry list, item 10. -/
theorem isProjFnShape_run {st : EStore} {n : NIdx} {x : ConLeche.Name}
    {r : Bool} {s s' : AState} (hok : StateOK s) (hs : s.store = st)
    (hd : denoteN st.ns n = some x)
    (hrun : NIdx.isProjFnShape n s = .ok (r, s')) :
    s' = s ∧ r = x.isProjFnShape := by
  sorry

/-! ## The per-declaration constant check -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal —
**THE declaration front door**, and what every arm of
`Bridge/Checker/Decl.lean` bottoms out in: the six guards, the annotation, the
inference and the sort test.

The conclusion is a refinement, as everywhere in this tier: an accepting arena
run gives an accepting pure run whose answer the arena's answer denotes.  The
guards are what make it non-trivial — each must be *exact*, not merely sound,
because the arena's acceptance has to imply con-leche's.

`sorry`: the six guards (`fe.find?` through `IFEnvOK`, `reservedBasisNames`
and `isProjFnShape` through the two lemmas above, `nameNodup`,
`looseBVarsBoundedFast` and `hasFvarFast` through `Bridge/ExprOps/Walks.lean`),
then `KnotSpec.annotate`, `allLevelParamsDefined_run`,
`constsResolveFFast_run`, `KnotSpec.infer` and
`EnsureSortSpec.ensureSort`, in that order.  Task #97-P3-Checker's sorry list,
item 11 — the single highest-value remaining proof of the tier, since all
seven arms wait on it. -/
theorem checkConstantVal_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {cv cvA : IConstantVal} {c : ConstantVal} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : checkConstantVal μ fe cv s = .ok (cvA, s')) :
    CoreStep μ env fe s s' ∧ ∃ cA F, Frontend.denoteCV s'.store cvA = some cA ∧
      ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env c = .ok cA := by
  sorry

/-! ## The three list checks

`checkTypedList`, `checkAnnotList` and `checkDefEqList` are the nested-pin and
iota-statement guards: list recursions over one `KnotSpec` clause each, with
nothing of their own.  Each is stated at the denoted lists, so the recursion
is `Frontend.denoteEList`'s. -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList.

`sorry`: a list induction over `KnotSpec.infer` and
`KnotSpec.defeq`.  Task #97-P3-Checker's sorry list, item 12. -/
theorem checkTypedList_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {depth : Nat} {as ts : List EIdx} {xs ys : List Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : CheckOK μ env fe s)
    (ha : Frontend.denoteEList s.store as = some xs)
    (ht : Frontend.denoteEList s.store ts = some ys)
    (hrun : checkTypedList μ fe depth as ts s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkTypedList (ConLeche.fueledOps μ F) env depth xs ys
        = .ok () := by
  sorry

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList.

`sorry`: a list induction over `KnotSpec.annotate` and `denoteE`'s
injectivity (the twin compares HANDLES where con-leche compares terms).  Task
#97-P3-Checker's sorry list, item 12. -/
theorem checkAnnotList_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {depth : Nat} {as : List EIdx} {xs : List Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : CheckOK μ env fe s)
    (ha : Frontend.denoteEList s.store as = some xs)
    (hrun : checkAnnotList μ fe depth as s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkAnnotList (ConLeche.fueledOps μ F) env depth xs = .ok () := by
  sorry

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList.

`sorry`: a list induction over `KnotSpec.defeq`.  Task
#97-P3-Checker's sorry list, item 12. -/
theorem checkDefEqList_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {depth : Nat} {as bs : List EIdx} {xs ys : List Expr}
    {s s' : AState} (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : CheckOK μ env fe s)
    (ha : Frontend.denoteEList s.store as = some xs)
    (hb : Frontend.denoteEList s.store bs = some ys)
    (hrun : checkDefEqList μ fe depth as bs s = .ok ((), s')) :
    CoreStep μ env fe s s' ∧ ∃ F,
      ConLeche.checkDefEqList (ConLeche.fueledOps μ F) env depth xs ys
        = .ok () := by
  sorry

end ConRon.Bridge
