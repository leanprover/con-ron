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
   and a `denoteFEnv` for the extended environment;
2. **the structural-`Nat` gate** — `natOpGuard` / `natOpStoredOkAll` /
   `certifyNatEqs`, run in the PRE-insertion environment with the operation's
   self-references replaced by its stored value;
3. **the `Nat.div`/`Nat.mod` variant gate** — `checkDivModPin`, whose loop is
   the one consumer of `Bridge/Checker/Base.lean`'s `orElseAttempt_run`;
4. **the compiler-trust gate** — `checkReducePin`.

**Why the pin gates are not `Bridge/Checker/Decl.lean`'s business.**  Each of
them runs AFTER the value check has already extended the environment, at the
extended index `fe2` and the pre-insertion one `fe` at once — con-leche's
`checkDivModPin ops pins env env2 c` and `checkReducePin ops env env2 c value`
take both for the same reason.  So each needs TWO `FoldOK`s related by a
`Pushed`, which is a shape nothing else in the tier has, and stating them here
keeps `Decl.lean`'s seven arms uniform.

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
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
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
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
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
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      IFEnvCoh fe' ∧ Pushed fe fe' ∧
      ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
        ConLeche.checkOpaqueVal (ConLeche.fueledOps μ F) env c x = .ok env' := by
  sorry

/-! ## The structural-`Nat` gate -/

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
    (hden : ∀ p ∈ eqs, ∃ q ∈ xs, denoteE s.store p.1 = some q.1 ∧
      denoteE s.store p.2 = some q.2)
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
    (hok : FoldOK μ env fe s) (hok2 : FoldOK μ env2 fe2 s)
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
    (hk : CoreSpec μ Arena.checkFuel) (hok : FoldOK μ env fe s) (hok2 : FoldOK μ env2 fe2 s)
    (hn : denoteN s.store.ns cn = some nm)
    (hv : denoteE s.store value = some x)
    (hrun : checkReducePin μ fe fe2 cn value s = .ok ((), s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ∃ F, ConLeche.checkReducePin (ConLeche.fueledOps μ F) env env2 nm x
        = .ok () := by
  sorry

end ConRon.Bridge
