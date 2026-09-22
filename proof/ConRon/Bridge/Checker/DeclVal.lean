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
   and a `denoteFEnv` for the extended environment.  Their state frame is
   `CoreStep` and not `StateOK` (task #97-P3-Checker-2): each CALLS the core,
   so the caches move, and what survives is the invariant at the environment
   the core ran at — which is the pre-insertion one, exactly as
   `checkConstantVal_bridge` concludes.  They also hand back
   `IFEnvOK env' fe' s'`, which is what the two pin gates below read `fe2`
   for;
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

**What the second one is, corrected** (task #97-P3-Checker-2).  The round that
stated these asked for `FoldOK μ env2 fe2 s` — and `FoldOK` carries
`PersIFEnv fe2`, which is **false**: `fe2` is the environment the value check
has just extended INSIDE the per-declaration bracket, so the constant it holds
carries a freshly interned, hence scratch, type.  It is task #97-P3-Ind's
finding at a second site.  What the gates actually read `fe2` for is
`reduceStoredOk fe2 c` / `divModEnvGuard fe2 c`, two index lookups and no core
call, so the clause they need is `IFEnvOK env2 fe2 s` and nothing more — and
that is what the three value checks above now hand back.

**Both gates only ever DECLINE or pass.**  Neither installs anything: their
result is `Unit` on both sides, and the environment the arm returns is the one
the value check produced.  That is why their bridge theorems have no
environment clause at all — they are the cheapest statements of the tier and
the most expensive proofs, because the certificates they check are pinned
terms the core must run on.
-/
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Decl

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

/-! ## The three value checks -/

/-- con-leche: ConLeche/Kernel/Checker.lean:32-50 checkDefnVal — a
definition's value against its checked constant, returning the pushed index.

`sorry`: `installValue_bridge` (`Bridge/Checker/Split.lean`),
`KnotSpec.infer`, `KnotSpec.defeq`, then `IFEnv.push`.  Task
#97-P3-Checker's sorry list, item 22. -/
theorem checkDefnVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {hint : ReducibilityHint} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : checkDefnVal μ fe cv value hint s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
        IFEnvOK env' fe' s' ∧
        ConLeche.checkDefnVal (ConLeche.fueledOps μ F) env c x hint = .ok env' := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal — **a theorem is
stored by its statement**: the constant keeps the record's RAW value as an
unread datum and the annotated value is a witness, checked and discarded.

`sorry`: `KnotSpec.infer`, `EnsureSortSpec.ensureSort`, the
is-a-proposition test (`lvlEq?` through `CacheOK.lvlEq`),
`installValue_bridge`, `KnotSpec.defeq`.  Task #97-P3-Checker's sorry
list, item 22. -/
theorem checkThmVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : checkThmVal μ fe cv value s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
        IFEnvOK env' fe' s' ∧
        ConLeche.checkThmVal (ConLeche.fueledOps μ F) env c x = .ok env' := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:84-107 checkOpaqueVal — the
theorem check without the is-a-proposition requirement; the result is stored
as an `axiomInfo`.

`sorry`: as `checkDefnVal_bridge`.  Task #97-P3-Checker's sorry list,
item 22. -/
theorem checkOpaqueVal_bridge {μ : CheckMode} {env : Env}
    {fe fe' : IFEnv} {cv : IConstantVal} {c : ConstantVal} {value : EIdx}
    {x : Expr} {s s' : AState}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : checkOpaqueVal μ fe cv value s = .ok (fe', s')) :
    CoreStep μ env fe s s' ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
        IFEnvOK env' fe' s' ∧
        ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env' := by
  sorry

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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:475-481 natOpNames — the seven
structural fast-path operations, off the pin table.

`sorry`: seven `pinAt_run`s, as `reservedBasisNames_run`
(`Bridge/Checker/Base.lean`) but without the interns.  Task #97-P3-Checker's
sorry list, item 13. -/
theorem natOpNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : natOpNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natOpNames := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:483-498 natDivModNames — the
eight WF-recursive operations, off the pin table.

`sorry`: eight `pinAt_run`s.  Task #97-P3-Checker's sorry list, item 13. -/
theorem natDivModNames_run {s s' : AState} {ns : List NIdx} (hp : PinsOK s)
    (hr : natDivModNames s = .ok (ns, s')) :
    s' = s ∧ denoteNL s.store ns ConLeche.natDivModNames := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:500-523 natOpDeps — the
operations involved in `c`'s recurrences.  The twin's dispatch is a chain of
HANDLE comparisons where con-leche's is a chain of name comparisons, so the
answer is exact for `denoteN_inj`'s reason.

`sorry`: fourteen `pinAt_run`s and `beq_handle_iff`
(`Bridge/Checker/Base.lean`) at each arm.  Task #97-P3-Checker's sorry list,
item 13. -/
theorem natOpDeps_run {cn : NIdx} {nm : ConLeche.Name} {ds : List NIdx}
    {s s' : AState} (hok : StateOK s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpDeps cn s = .ok (ds, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ denoteNL s'.store ds (ConLeche.natOpDeps nm) := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpGuard) — the
structural-`Nat` environment guard is con-leche's at the denoted environment.

`sorry`: `natLitSupported` / `natOpDepsStored` / the `Bool`-family lookups
through `IFEnvOK`, then `natOpDeps_run`.  Task #97-P3-Checker's sorry list,
item 23. -/
theorem natOpGuard_run {env2 : Env} {fe2 : IFEnv} {cn : NIdx}
    {nm : ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hie : IFEnvOK env2 fe2 s) (hn : denoteN s.store.ns cn = some nm)
    (hr : natOpGuard fe2 cn s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.natOpGuard env2 nm := by
  sorry

/-- con-leche: ConLeche/Kernel/CoreDefs.lean (natOpStoredOk) — the twin's list
recursion answers con-leche's `List.all` (DESIGN §3.4 forbids the closure).

`sorry`: a list induction over `natOpStoredOk`'s own `IFEnvOK` reads.  Task
#97-P3-Checker's sorry list, item 23. -/
theorem natOpStoredOkAll_run {env2 : Env} {fe2 : IFEnv} {ds : List NIdx}
    {xs : List ConLeche.Name} {r : Bool} {s s' : AState} (hok : StateOK s)
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

`sorry`: a list recursion over `Bridge/ExprOps/**`'s `substConst0` spec.  Task
#97-P3-Checker's sorry list, item 23. -/
theorem substConst0Pairs_run {cn : NIdx} {nm : ConLeche.Name} {rh : EIdx}
    {x : Expr} {eqs r : List (EIdx × EIdx)} {xs : List (Expr × Expr)}
    {s s' : AState} (hok : StateOK s) (hn : denoteN s.store.ns cn = some nm)
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

`sorry`: a list induction over `KnotSpec.defeq`, plus
`substConst0Pairs` and `natOpEquations`' exactness (both are pinned-term
constructions, so both are `Bridge/Checker/Basis.lean`'s shape).  Task
#97-P3-Checker's sorry list, item 23. -/
theorem certifyNatEqs_bridge {μ : CheckMode} {env : Env}
    {fe : IFEnv} {eqs : List (EIdx × EIdx)} {xs : List (Expr × Expr)}
    {r : Bool} {s s' : AState} (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (hok : FoldOK μ env fe s)
    (hden : EqPairsDenote s.store eqs xs)
    (hws : ∀ q ∈ xs, Expr.WScoped 2 q.1 ∧ Expr.WScoped 2 q.2)
    (hrun : certifyNatEqs μ fe eqs s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧
      (r = true → ∃ F, ConLeche.certifyNatEqs (ConLeche.fueledOps μ F) env xs
        = .ok true) := by
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
    (hok : FoldOK μ env fe s) (hok2 : IFEnvOK env2 fe2 s)
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
    (hok2 : IFEnvOK env2 fe2 s)
    (hn : denoteN s.store.ns cn = some nm)
    (hv : denoteE s.store value = some x)
    (hrun : checkReducePin μ fe fe2 cn value s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x
        = .ok () := by
  sorry

end ConRon.Bridge
