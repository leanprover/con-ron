/-
# `ConRon.Bridge.Core.Walks.Spec` — the shape of a non-slot walk's theorem

`Bridge/Core/Knot.lean` fixes ONE shape for the six
bodies (`BodySpec`, `BodySpecV`) because all six take one or two `EIdx`
subjects and answer an `EIdx` or a `Bool`.  The ~110 walks of
`Arena/Core.lean` that are not knot slots do not: they answer `Option EIdx`
(`unfoldDefinition`, `reduceNat`, `iotaRec`), `LIdx` (`ensureSort`),
`List EIdx` (`etaProjs`), `Bool` at one subject, at
two, at a pair of LISTS, at no subject at all.

So this module does not fix a body shape; it fixes the **answer relation**,
and every walk's theorem is then `⦃s = s₀⦄ walk … ⦃fun r s' => CheckOK … ∧
Ext … ∧ <answer relation>; ⊤⦄` with the pure side's fuel abstracted into one
argument.

## The abstraction: the pure call, minus its fuel

`Bridge/Core/Knot.lean`'s `SimE op d e st' r` reads `∃ F, op F d e = .ok v`.
The walks' pure comparands do not share `op`'s arity — `ConLeche.iotaRec`
takes the mode, the fueled record, the environment, the depth and the
subject; `ConLeche.projCertAt` takes two `Bool` switches besides — so the
relations below take the pure call **already applied to everything but the
fuel**, as a `Nat → CheckM α`.  `SimE` and `SimV` are the `d`-and-`e`-applied
instances of `SimEOp` and `SimBOp` (definitionally), which is what lets an
arm of a body theorem hand a walk theorem's conclusion straight to
`Bridge/Core/Knot.lean`'s.

## The well-scopedness conjunct, and why it is not everywhere

`SimE` carries `Expr.WScoped d v` because the memo insert needs it (see
`Bridge/Core/Knot.lean`).  A walk's answer needs it exactly when the answer
is fed back into a knot slot: `unfoldDefinition`'s reduct is (`whnfStep`
hands it to `whnfLoop`, which calls `whnfCore`), `headHint`'s hint is
not.  So `SimEOp` and `SimOOp` carry it and `SimBOp` does not.
-/
import ConRon.Bridge.Core.Knot

namespace ConRon.Bridge.Core

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## 1. The three answer relations -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — **the handle-valued walk
answer**: the answer handle denotes a well-scoped `v` that the pure call
produces at some fuel.  `Bridge/Core/Knot.lean`'s `SimE` is this at
`fun F => op F d e`. -/
def SimEOp (P : Nat → CheckM Expr) (d : Nat) (st' : EStore) (r : EIdx) :
    Prop :=
  ∃ v, denoteE st' r = some v ∧ Expr.WScoped d v ∧ ∃ F, P F = .ok v

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — **the optional-handle
answer** (`unfoldDefinition`, `reduceNat`, `iotaRec`): `none` denotes `none`,
and a `some` denotes the pure call's own `some`.  `denoteEO`
(`Bridge/Rel.lean`) is what makes the two shapes literally the same. -/
def SimOOp (P : Nat → CheckM (Option Expr)) (d : Nat) (st' : EStore)
    (r : Option EIdx) : Prop :=
  ∃ v, denoteEO st' r = some v ∧ (∀ x, v = some x → Expr.WScoped d x) ∧
    ∃ F, P F = .ok v

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — **the `Bool`-valued
answer**, which names no handle and therefore needs no target store.
`Bridge/Core/Knot.lean`'s `SimV` is this at `fun F => op F d a b`. -/
def SimBOp (P : Nat → CheckM Bool) (x : Bool) : Prop := ∃ F, P F = .ok x

end ConRon.Bridge.Core
