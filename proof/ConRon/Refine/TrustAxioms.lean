import ConRon.Refine.CoreKPinned
import ConLeche.Kernel.DeclCheck

/-! # `kernel::trust_axioms` and `kernel::trust_pins` — the compiler-trust
family (task #56)

`CORE_PLAN.md` step 7.  Two Rust modules, one file: `trust_axioms.rs`
(`ConLeche/Kernel/TrustAxioms.lean`, 30 public functions) and `trust_pins.rs`
(`ConLeche/Kernel/TrustPins.lean`, 2) — the pinned names, the pinned shapes of
`Lean.trustCompiler` / `Lean.reduceNat` / `Lean.reduceBool` /
`Lean.ofReduceNat` / `Lean.ofReduceBool`, the guards that check a stream's
declaration against them, and the two hand-pinned identity values the reduce
operations' install compares against.

## The pins are the RAW ones, and that is exact (task #24)

`TrustAxioms.lean` writes its pins twice: the raw ones, hand-written with
`Basis/Builder.lean`'s DSL (`reduceOpRaw`, `ofReduceRaw`), and the annotated
ones (`reduceNatCvA`, `reduceBoolCvA`, `ofReduceNatA`, `ofReduceBoolA`)
computed from them at elaboration time by `#annotate_pins`.  Every consumer
goes through `ConstantVal.matchesPin`, whose type test is
`a.erasePw == b.erasePw`, so `matchesPin cv (annotate pin) = matchesPin cv pin`
and the port compares against the raw pin, which it can write down, with the
annotated twin cited on the same item (DESIGN.md task #24).

Here that argument is not an argument at all but a **closed computation**:
`reduceOpCvA_erasePw` and `ofReducePinA_erasePw` below are `rfl` — the four
annotated pins and the raw ones they came from have the same name, the same
(empty) level parameters and `erasePw`-equal types.  (`reduceNatCvA` is in
fact *literally* `reduceOpRaw reduceNatName`: its one binder's codomain is a
`.const`, so `annotPwPi` answers the parse placeholder `.never` the raw pin
already carries.  The two `ofReduce*` pins differ from their raw forms in
exactly the three binder data `erasePw` erases.)  So each pin builder's lemma
is the closed equality against the **raw** con-leche pin, and each guard's
lemma is exactness against the cited Lean guard *as written* — with the
annotated pin in it.

## The `F`-twins, and what is stated against what

`DeclCheck.lean:272-308` has an `FEnv`-indexed twin of every environment
predicate here (`trustCompilerOkF`, `reduceStoredOkF`, `reduceElemOkF`,
`ofReduceAxOkF`, `reducePinGuardF`), and the port has one environment
spelling, the index (task #18's deviation 3), so every guard below is stated
against the `F`-twin, over `CoreKBase`'s find-agreement projection
(`FindAgree`/`FindWF`).  The two guards the port *factors out* of a `&&`
cascade — `true_pinned` and `true_intro_pinned` (task #3's pattern 9) — have
no Lean twin of their own and are stated against the matching conjunct of
`trustCompilerOkF`, spelled out.

`reduce_pin_guard` is the one guard whose last conjunct the port reaches
through `core_k::consts_resolve`, whose refinement (`Refine/CoreKSupport.lean`)
is against the `Env`-indexed `Expr.constsResolve`; it therefore carries
`CoreKSupport`'s own `henv` hypothesis (`lfe.find? = lenv.find?`), and the
conclusion is the `F`-twin, the two being the same clauses.

## The two hypotheses this file imports

Task #56's files are written in parallel, so — exactly as task #49's eleven
`CoreK*` files did — what a sibling owns travels as an explicit hypothesis of
the lemma that needs it:

* **`MatchesPinSpec`**: `std_axioms::matches_pin_fast` is `ConstantVal.matchesPin`.
  It is `Refine/StdAxioms.lean`'s (`Expr.erasePwEq_eq` is con-leche's own
  agreement between the lockstep descent and the specification).
* **`BasisPinsSpec`**: `basis_pins::eq_basis_pinned` / `nat_basis_pinned` are
  `decide (fe.find? eqName = some eqA)` / `decide (fe.find? natName = some natA)`
  — the two pins compared by exact `ConstantInfo` equality rather than through
  `matchesPin`, which is why they have a module of their own.

Neither is a new claim; both are discharged where the sibling lands.

## Deviations recorded

`lean_ns` has no con-leche declaration to cite: Lean spells
`anonymous |>.str "Lean"` inline at each of the five names below it.  Its lemma
is against that prefix.  `eq_app` is `ofReduceRaw`'s local `eqApp` lambda,
which §3.4 forbids, so it is a named function with the same citation.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel
open ConRon.Refine.CoreK

namespace ConRon.Refine.TrustAxioms

/-! ## The two imported hypotheses -/

/-- **`std_axioms::matches_pin_fast` is `ConstantVal.matchesPin`, exactly.**
Task #56's sibling `Refine/StdAxioms.lean` proves it; `matchesPinFast` is
con-leche's own `@[csimp]` replacement for `matchesPin`, and
`Expr.erasePwEq_eq` (`StdAxioms.lean:206-210`) is the agreement. -/
def MatchesPinSpec : Prop :=
  ∀ (cv pin : env.ConstantVal) (r : Bool), ConstantValWF cv → ConstantValWF pin →
    std_axioms.matches_pin_fast cv pin = ok r →
      r = ConLeche.ConstantVal.matchesPin (absConstantVal cv) (absConstantVal pin)

/-- **The two exactly-compared basis pins**, `Refine/BasisPins.lean`'s
(`kernel/basis_pins.rs` over task #22's generated table): the whole guard
`decide (fe.find? eqName = some eqA)` resp. `… natName = some natA`. -/
structure BasisPinsSpec (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop where
  eqPinned : ∀ r : Bool, basis_pins.eq_basis_pinned fe = ok r →
    r = decide (lfe.find? ConLeche.eqName = some ConLeche.eqA)
  natPinned : ∀ r : Bool, basis_pins.nat_basis_pinned fe = ok r →
    r = decide (lfe.find? ConLeche.natName = some ConLeche.natA)

/-! ## The annotated pins are the raw ones, under `matchesPin`

The four closed computations DESIGN.md task #24's argument predicts.  Nothing
below ever names an annotation pass: `#annotate_pins`' output is a closed term
and `Expr.erasePw` of it is the raw pin's, by `rfl`. -/

/-- `reduceOpCvA c` — the annotated pin — is `matchesPin`-indistinguishable
from the raw `reduceOpRaw` at the same operation, which is what the port
returns (`TrustAxioms.lean:146-148 reduceOpCvA`, `:137-139` the
`#annotate_pins` command). -/
theorem matchesPin_reduceOpCvA (cv : ConLeche.ConstantVal) (c : ConLeche.Name) :
    ConLeche.ConstantVal.matchesPin cv (ConLeche.reduceOpCvA c)
      = ConLeche.ConstantVal.matchesPin cv
          (if c = ConLeche.reduceNatName then ConLeche.reduceOpRaw ConLeche.reduceNatName
           else ConLeche.reduceOpRaw ConLeche.reduceBoolName) := by
  rw [ConLeche.reduceOpCvA]
  split
  · rfl
  · rfl

/-- The same for `ofReducePinA` (`TrustAxioms.lean:150-152 ofReducePinA`,
`:141-144` the `#annotate_pins` command).  Here the annotated pin genuinely
differs from the raw one — its three binders carry `.ifAllZero []` where the
raw pin carries `.never` — and that is exactly what `erasePw` erases. -/
theorem matchesPin_ofReducePinA (cv : ConLeche.ConstantVal) (n : ConLeche.Name) :
    ConLeche.ConstantVal.matchesPin cv (ConLeche.ofReducePinA n)
      = ConLeche.ConstantVal.matchesPin cv
          (if n = ConLeche.ofReduceNatName then ConLeche.ofReduceRaw ConLeche.ofReduceNatName
           else ConLeche.ofReduceRaw ConLeche.ofReduceBoolName) := by
  rw [ConLeche.ofReducePinA]
  split
  · rfl
  · rfl

end ConRon.Refine.TrustAxioms
