/-
# `ConRon.Bridge.Core.Walks.Spec` — the shape of a non-slot walk's theorem

Task #97-P3-CoreWalks.  `Bridge/Core/Knot.lean` fixes ONE shape for the six
bodies (`BodySpec`, `BodySpecV`) because all six take one or two `EIdx`
subjects and answer an `EIdx` or a `Bool`.  The ~110 walks of
`Arena/Core.lean` that are not knot slots do not: they answer `Option EIdx`
(`unfoldDefinition`, `reduceNat`, `iotaRec`), `LIdx` (`ensureSort`),
`PropWhen` (`annotPwPi`), `List EIdx` (`etaProjs`), `Bool` at one subject, at
two, at a pair of LISTS, at no subject at all.

So this module does not fix a body shape; it fixes the **answer relation**,
and every walk's theorem is then `⦃s = s₀⦄ walk … ⦃⇓? r s' => ⌜CheckOK … ∧
Ext … ∧ <answer relation>⌝⦄` with the pure side's fuel abstracted into one
argument.

## The abstraction: the pure call, minus its fuel

`Bridge/Core/Knot.lean`'s `SimE op d e st' r` reads `∃ F, op F d e = .ok v`.
The walks' pure comparands do not share `op`'s arity — `ConLeche.iotaRec`
takes the mode, the fueled record, the environment, the depth and the
subject; `ConLeche.projCertAt` takes two `Bool` switches besides — so the
relations below take the pure call **already applied to everything but the
fuel**, as a `Nat → CheckM α`.  `SimE` and `SimV` are the `d`-and-`e`-applied
instances of `SimEOp` and `SimBOp`, and the two bridging lemmas below say so,
which is what lets an arm of a body theorem hand a walk theorem's conclusion
straight to `Bridge/Core/Knot.lean`'s.

## The well-scopedness conjunct, and why it is not everywhere

`SimE` carries `Expr.WScoped d v` because the memo insert needs it (see
`Bridge/Core/Knot.lean`).  A walk's answer needs it exactly when the answer
is fed back into a knot slot: `unfoldDefinition`'s reduct is (`whnfStep`
hands it to `whnfLoop`, which calls `whnfCore`), `annotPwPi`'s `PropWhen` is
not.  So `SimEOp` and `SimOOp` carry it and `SimBOp`/`SimLOp`/`SimVOp` do
not.
-/
import ConRon.Bridge.Core.Knot

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ## 1. The five answer relations -/

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

/-- con-leche: ConLeche/Verify/SimI.lean:254 RelL — **the level-valued
answer** (`ensureSort`). -/
def SimLOp (P : Nat → CheckM Level) (st' : EStore) (r : LIdx) : Prop :=
  ∃ u, denoteL st'.ls r = some u ∧ ∃ F, P F = .ok u

/-- con-leche: ConLeche/Verify/SimI.lean:252 RelV — **the
representation-free answer at any type** (`annotPwPi`'s `PropWhen`,
`headHint`'s `ReducibilityHint`, `rawNatLit?`'s `Option Nat`): the arena's
value IS con-leche's, because the type is one both tiers share. -/
def SimVOp {α : Type} (P : Nat → CheckM α) (x : α) : Prop := ∃ F, P F = .ok x

/-! ## 2. The bridges to `Bridge/Core/Knot.lean`'s two

One `Iff` each, both `Iff.rfl`: the definitions are the same proposition with
the pure call's arguments moved into the abstraction.  They exist so that an
arm of a body theorem can `exact` a walk theorem's conclusion rather than
`obtain`/`refine` it apart. -/

/-- con-leche: none — `SimE` IS `SimEOp` at the applied call. -/
theorem SimE_eq_SimEOp (op : Nat → Nat → Expr → CheckM Expr) (d : Nat)
    (e : Expr) (st' : EStore) (r : EIdx) :
    SimE op d e st' r ↔ SimEOp (fun F => op F d e) d st' r := Iff.rfl

/-- con-leche: none — `SimV` IS `SimBOp` at the applied call. -/
theorem SimV_eq_SimBOp (op : Nat → Nat → Expr → Expr → CheckM Bool) (d : Nat)
    (a b : Expr) (x : Bool) :
    SimV op d a b x ↔ SimBOp (fun F => op F d a b) x := Iff.rfl

/-! ## 3. The eliminators

`Bridge/Rel.lean`'s five, in the shapes above.  `SimBOp`, `SimLOp` and
`SimVOp` need `.ext` only where a store appears, which is `SimLOp`. -/

/-- con-leche: none — the answer survives an arena extension. -/
theorem SimEOp.ext {P : Nat → CheckM Expr} {d : Nat} {st st' : EStore}
    {r : EIdx} (h : SimEOp P d st r) (hx : Ext st st') : SimEOp P d st' r := by
  obtain ⟨v, hv, hw, F, hF⟩ := h
  exact ⟨v, denote_ext hv hx, hw, F, hF⟩

/-- con-leche: none — the optional answer survives an arena extension. -/
theorem SimOOp.ext {P : Nat → CheckM (Option Expr)} {d : Nat}
    {st st' : EStore} {r : Option EIdx} (h : SimOOp P d st r)
    (hx : Ext st st') : SimOOp P d st' r := by
  obtain ⟨v, hv, hw, F, hF⟩ := h
  refine ⟨v, ?_, hw, F, hF⟩
  cases r with
  | none => exact hv
  | some j =>
    simp only [denoteEO] at hv ⊢
    cases hj : denoteE st j with
    | none => rw [hj] at hv; simp at hv
    | some x => rw [denote_ext hj hx]; rw [hj] at hv; exact hv

/-- con-leche: none — the level answer survives an arena extension. -/
theorem SimLOp.ext {P : Nat → CheckM Level} {st st' : EStore} {r : LIdx}
    (h : SimLOp P st r) (hx : Ext st st') : SimLOp P st' r := by
  obtain ⟨u, hu, F, hF⟩ := h
  exact ⟨u, hx.lss.ls.lvl _ _ hu, F, hF⟩

/-- con-leche: none — the answer's denotation, forgetting the pure run: what
a caller that only needs the handle to decode asks for. -/
theorem SimEOp.denote {P : Nat → CheckM Expr} {d : Nat} {st : EStore}
    {r : EIdx} (h : SimEOp P d st r) : (denoteE st r).isSome = true := by
  obtain ⟨v, hv, _, _, _⟩ := h
  rw [hv]; rfl

/-- con-leche: none — the answer's well-scopedness at a KNOWN denotation,
which is the precondition of feeding it into a second slot. -/
theorem SimEOp.wscoped {P : Nat → CheckM Expr} {d : Nat} {v : Expr}
    {st : EStore} {r : EIdx} (h : SimEOp P d st r)
    (hv : denoteE st r = some v) : Expr.WScoped d v := by
  obtain ⟨v', hv', hw, _, _⟩ := h
  rw [hv] at hv'
  obtain rfl := Option.some.inj hv'
  exact hw

/-- con-leche: none — **the `none` answer**: the walk declined and so did the
pure call.  The shape three of the four `Option`-valued walks exit by. -/
theorem SimOOp.of_none {P : Nat → CheckM (Option Expr)} {d : Nat}
    {st : EStore} {F : Nat} (h : P F = .ok Option.none) :
    SimOOp P d st Option.none := by
  refine ⟨Option.none, rfl, ?_, F, h⟩
  intro x hx
  exact absurd hx (by simp)

/-- con-leche: none — **the `some` answer**: the walk produced a handle and
the pure call produced its denotation. -/
theorem SimOOp.of_some {P : Nat → CheckM (Option Expr)} {d : Nat}
    {st : EStore} {j : EIdx} {v : Expr} (hv : denoteE st j = Option.some v)
    (hw : Expr.WScoped d v) {F : Nat} (h : P F = .ok (Option.some v)) :
    SimOOp P d st (Option.some j) := by
  refine ⟨Option.some v, ?_, ?_, F, h⟩
  · simp only [denoteEO, hv, Option.map_some]
  · intro x hx
    cases hx
    exact hw


/-- con-leche: none — **the `some` answer, read backwards**: a walk that
answered a handle denotes it, and the pure call answered that denotation.
The inverse of `SimOOp.of_some`, and what a CALLER of an `Option`-valued walk
(`whnfStep`'s two) needs to continue on the reduct. -/
theorem SimOOp.some_inv {P : Nat → CheckM (Option Expr)} {d : Nat}
    {st : EStore} {j : EIdx} (h : SimOOp P d st (Option.some j)) :
    ∃ v, denoteE st j = Option.some v ∧ Expr.WScoped d v ∧
      ∃ F, P F = .ok (Option.some v) := by
  obtain ⟨w, hw, hsc, F, hF⟩ := h
  simp only [denoteEO, Option.map_eq_some_iff] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  exact ⟨v, hv, hsc v rfl, F, hF⟩

/-- con-leche: none — **the `none` answer, read backwards**. -/
theorem SimOOp.none_inv {P : Nat → CheckM (Option Expr)} {d : Nat}
    {st : EStore} (h : SimOOp P d st Option.none) :
    ∃ F, P F = .ok Option.none := by
  obtain ⟨w, hw, _, F, hF⟩ := h
  simp only [denoteEO] at hw
  obtain rfl := Option.some.inj hw
  exact ⟨F, hF⟩

/-! ## 4. The axiom census -/

section Census

#print axioms SimE_eq_SimEOp
#print axioms SimV_eq_SimBOp
#print axioms SimEOp.ext
#print axioms SimOOp.ext
#print axioms SimLOp.ext
#print axioms SimEOp.denote
#print axioms SimEOp.wscoped
#print axioms SimOOp.of_none
#print axioms SimOOp.of_some
#print axioms SimOOp.some_inv
#print axioms SimOOp.none_inv

end Census

end ConRon.Bridge.Core
