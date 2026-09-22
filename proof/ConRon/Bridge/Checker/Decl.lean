/-
# `ConRon.Bridge.Checker.Decl` — `checkDecl`'s seven arms, one theorem each

`Arena/Checker.lean`'s `checkDecl` is a seven-way match, and this module is
one bridge theorem per arm, all with the same conclusion (`DeclOut` below).
`Bridge/Checker/Fold.lean`'s `Arena.checkDecl_bridge` is then `cases pd` and
nothing else, which is what keeps the per-declaration theorem — the one DESIGN
§8.2 states — free of arm-specific hypotheses.

## What an arm concludes, and what it deliberately does not

`DeclOut` has six clauses and the last is §8.2's:

    ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
      ConLeche.checkDecl μ (fueledOps μ F) pinsP env d = .ok env'

The five before it are the plumbing the FOLD needs and the arm is the only
place that can supply: the store invariant survives, the arena only grew, the
pin table is untouched, the index is still its list's index, and **the step
only pushed** (`Pushed`, `Bridge/Promote/Exact.lean`) — which is what makes
`checkDeclStep`'s promotion counter `k` mean "the constants this step
installed".

There is **no persistence clause**: `checkDecl` does not promote.  The
environment it hands back names scratch handles, and it is `promoteNew`'s job
— one level up, in `checkDeclStep` — to make it persistent before
`dropScratch`.  Writing `PersIFEnv` into `DeclOut` would be stating a
falsehood about the very deviation task #97-P6-2 introduced.

## The pins

`pins : List INatOpPinSet` on the arena side and `pinsP : List NatOpPinSet` on
con-leche's are related by `PinsDenote`, interned once by `internAllPins`
before the fold starts (`Bridge/Checker/Pins.lean`).  They are a PARAMETER of
`checkDecl` on both sides and no arm changes them, so the relation is a
standing hypothesis of every theorem here.

## The sorry list

The seven arms are the tier's remaining proof obligations, and each needs a
different thing:

| arm | what it needs |
|---|---|
| `defn` | `checkConstantVal` + `checkDefnVal` + the two `Nat`-pin gates |
| `thm` / `opaque` | `checkConstantVal` + the value check; `opaque` also the `reduce*` pin gate |
| `axiom` | `Bridge/Checker/Canon.lean`'s `canonEq` and the four standard/trust shape tests |
| `basis` | `Bridge/Checker/Basis.lean`'s `checkBasisDecl` |
| `ind` | **nothing here** — it is `IndSpec`, the named hypothesis |
| `quot` | `quotPinHit`'s exactness |

Every one of them bottoms out in `checkConstantVal_bridge`
(`Bridge/Checker/Base.lean`), which bottoms out in `KnotSpec`.
-/
import ConRon.Bridge.Checker.Hyp

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The interned pin variants denote -/

/-- con-leche: ConLeche/Kernel/NatOpPinSet.lean:31-50 NatOpPinSet — one
interned pin variant denotes con-leche's: the toolchain string is carried
verbatim and each of the sixteen terms denotes its counterpart. -/
structure PinSetDenote (st : EStore) (p : INatOpPinSet) (q : NatOpPinSet) :
    Prop where
  toolchain : p.toolchain = q.toolchain
  divPin : denoteE st p.divPin = some q.divPin
  modPin : denoteE st p.modPin = some q.modPin
  gcdPin : denoteE st p.gcdPin = some q.gcdPin
  landPin : denoteE st p.landPin = some q.landPin
  lorPin : denoteE st p.lorPin = some q.lorPin
  xorPin : denoteE st p.xorPin = some q.xorPin
  shiftLeftPin : denoteE st p.shiftLeftPin = some q.shiftLeftPin
  shiftRightPin : denoteE st p.shiftRightPin = some q.shiftRightPin
  divProofs : Frontend.denoteEList st p.divProofs = some q.divProofs
  modProofs : Frontend.denoteEList st p.modProofs = some q.modProofs
  gcdProofs : Frontend.denoteEList st p.gcdProofs = some q.gcdProofs
  landProofs : Frontend.denoteEList st p.landProofs = some q.landProofs
  lorProofs : Frontend.denoteEList st p.lorProofs = some q.lorProofs
  xorProofs : Frontend.denoteEList st p.xorProofs = some q.xorProofs
  shiftLeftProofs : Frontend.denoteEList st p.shiftLeftProofs
    = some q.shiftLeftProofs
  shiftRightProofs : Frontend.denoteEList st p.shiftRightProofs
    = some q.shiftRightProofs

/-- con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _ — the interned pin LIST
denotes con-leche's, variant by variant and in order (the order is the order
the install gate tries them, so it is part of the statement). -/
def PinsDenote (st : EStore) : List INatOpPinSet → List NatOpPinSet → Prop
  | [], [] => True
  | p :: ps, q :: qs => PinSetDenote st p q ∧ PinsDenote st ps qs
  | _, _ => False

/-- con-leche: none — the pin list's denotation transports across an
append. -/
theorem PinsDenote.mono {st st' : EStore} (hx : Ext st st') :
    ∀ ps qs, PinsDenote st ps qs → PinsDenote st' ps qs := by
  intro ps
  induction ps with
  | nil => intro qs h; cases qs <;> exact h
  | cons a as ih =>
    intro qs h
    cases qs with
    | nil => exact h
    | cons b bs =>
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ih bs h2⟩
      exact {
        toolchain := h1.toolchain
        divPin := hx.expr _ _ h1.divPin
        modPin := hx.expr _ _ h1.modPin
        gcdPin := hx.expr _ _ h1.gcdPin
        landPin := hx.expr _ _ h1.landPin
        lorPin := hx.expr _ _ h1.lorPin
        xorPin := hx.expr _ _ h1.xorPin
        shiftLeftPin := hx.expr _ _ h1.shiftLeftPin
        shiftRightPin := hx.expr _ _ h1.shiftRightPin
        divProofs := denoteEList_ext hx _ _ h1.divProofs
        modProofs := denoteEList_ext hx _ _ h1.modProofs
        gcdProofs := denoteEList_ext hx _ _ h1.gcdProofs
        landProofs := denoteEList_ext hx _ _ h1.landProofs
        lorProofs := denoteEList_ext hx _ _ h1.lorProofs
        xorProofs := denoteEList_ext hx _ _ h1.xorProofs
        shiftLeftProofs := denoteEList_ext hx _ _ h1.shiftLeftProofs
        shiftRightProofs := denoteEList_ext hx _ _ h1.shiftRightProofs }

/-! ## What an arm concludes -/

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**the per-declaration bridge's conclusion**, at one `checkDecl` call.
DESIGN §8.2's statement is the last clause; the five before it are what the
fold needs and only the arm can supply.

`Ext` and not `PExt` here, deliberately: `checkDecl` appends and never drops,
so the TOTAL extension holds, and `checkDeclStep` is where it weakens
(`Bridge/Promote/Pers.lean`). -/
structure DeclOut (μ : CheckMode) (pinsP : List NatOpPinSet) (env : Env)
    (d : Declaration) (s : AState) (fe fe' : IFEnv) (s' : AState) : Prop where
  state : StateOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins
  coh : IFEnvCoh fe'
  pushed : Pushed fe fe'
  run : ∃ env' F, denoteFEnv s'.store fe' = some env' ∧
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env'

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

`sorry`: `checkConstantVal_bridge` and `checkThmVal_bridge`.  Task
#97-P3-Checker's sorry list, item 7. -/
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
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:491-500 checkDecl (the
`.opaqueDecl` arm), with the compiler-trust `reduce*` gate behind it.

`sorry`: `checkConstantVal_bridge`, `checkOpaqueVal_bridge` and
`checkReducePin`.  Task #97-P3-Checker's sorry list, item 7. -/
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
  sorry

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

`sorry`: `checkBasisDecl_bridge` (`Bridge/Checker/Basis.lean`).  Task
#97-P3-Checker's sorry list, item 7. -/
theorem checkDecl_bridge_basis {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {kind : BasisKind}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hrun : Arena.checkDecl μ pins fe (.basisDecl kind) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.basisDecl kind) s fe fe' s' := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:564-600 checkDecl (the `.indDecl`
arm) — **the one arm this tier does not own**.  The recogniser
(`basisPinHit`) is `Bridge/Checker/Basis.lean`'s and the route behind it is
`IndSpec`, the named hypothesis.

`sorry`: `basisPinHit`'s exactness, and then `IndSpec.run` verbatim.  Task
#97-P3-Checker's sorry list, item 7 — the only one of the seven whose
remaining content is a *hypothesis* rather than a proof. -/
theorem checkDecl_bridge_ind {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {nP : Nat}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (hind : IndSpec μ)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : Arena.checkDecl μ pins fe (.indDecl block nP) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.indDecl b nP) s fe fe' s' := by
  sorry

/-- con-leche: ConLeche/Kernel/Checker.lean:602-626 checkDecl (the `.quotDecl`
arm) — the four-record quotient package, the first matching record installing
the pinned block whole.

`sorry`: `quotPinHit`'s exactness (`Bridge/Checker/Basis.lean`) and
`checkBasisDecl_bridge` at `.quotK`.  Task #97-P3-Checker's sorry list,
item 7. -/
theorem checkDecl_bridge_quot {μ : CheckMode}
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {k : QuotKind} {cv : IConstantVal}
    {c : ConstantVal}
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (hok : FoldOK μ env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hrun : Arena.checkDecl μ pins fe (.quotDecl k cv) s = .ok (fe', s')) :
    DeclOut μ pinsP env (.quotDecl k c) s fe fe' s' := by
  sorry

end ConRon.Bridge
