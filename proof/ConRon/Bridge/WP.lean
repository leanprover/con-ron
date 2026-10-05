/-
# `ConRon.Bridge.WP` — the `Std.Do` triples of this tier, read by `vcgen`

Lean 4.35 deprecated `mvcgen` for `vcgen` (task #111).  The two are not the
same tactic on a new name: `mvcgen` generates verification conditions for
`Std.Do.Triple` goals (an `SPred` precondition, a `PostCond` postcondition),
and `vcgen` for `Std.WP.Triple` goals (a precondition in any complete
lattice — here `AState → Prop` — a plain postcondition function, and a
separate exception postcondition).  `vcgen` rejects a `Std.Do` goal outright
("could not determine the program type of the goal"), and the `@[spec]`
attribute files a `Std.Do` triple in the legacy database only, which
`vcgen` does not read.

Every statement of this tier is a `Std.Do` triple of one shape (DESIGN
§8.6's template, `Bridge/Specs.lean`):

```lean
⦃fun s => ⌜P s⌝⦄ x ⦃⇓? r s' => ⌜Q r s'⌝⦄       -- x : AM α
```

and for `AM = StateT AState (Except CheckError)` that is *literally* the
`Std.WP` triple `Triple x P Q (fun _ => True)` — the `⇓?` is the exception
postcondition `⊤`.  This module is the bridge, in three pieces, so that no
statement changes:

* `AM.do_of_wp` turns a `Std.Do` goal into the `Std.WP` one, so that a proof
  starts `to_wp; vcgen [...]` (`to_wp` is `apply AM.do_of_wp` plus a zeta
  reduction, below);
* `@[wp_spec]` on a `Std.Do` spec theorem `f_spec` derives its `Std.WP`
  twin `f_spec.wp` (by `AM.wp_of_do`) and files THAT under `@[spec]`, so
  `vcgen` finds it;
* `wp% h` does the same for a local hypothesis (an induction hypothesis, a
  `Spec` record's field) passed in `vcgen [wp% h]`.

The order instances on `Prop` are `scoped` in `Std.WP` (they come with its
triple notation, which would clash with `Std.Do`'s `⦃⦄`), so this module
re-scopes the two instances `vcgen` needs into `ConRon.Bridge`.
-/
import ConRon.Arena
import Std.Tactic.Do
import Std.WP

namespace ConRon.Bridge

open Lean Elab Meta Std.Do ConRon.Arena

attribute [scoped instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

/-- con-leche: none — **a `Std.WP` triple proves the `Std.Do` one** of the
same pre- and postcondition, for `AM` under partial correctness.  The goal
side of the bridge: `apply AM.do_of_wp` hands `vcgen` its own goal. -/
theorem AM.do_of_wp {α : Type} {x : AM α} {P : AState → Prop}
    {Q : α → AState → Prop} (h : Std.WP.Triple x P Q (fun _ => True)) :
    ⦃fun s => ⌜P s⌝⦄ x ⦃⇓? r s => ⌜Q r s⌝⦄ := by
  obtain ⟨h⟩ := h
  intro s hs
  have hwp := h s hs
  simp only [Std.WP.StateT.wp_apply_eq, StateT.run] at hwp
  cases hx : x s with
  | error e =>
    simp [wp, Except.instWP._aux_1, StateT.run, hx, ExceptT.run, Id.run,
      ExceptConds.true, ExceptConds.const]
  | ok p =>
    simp [hx, Std.WP.wp, Std.WP.WP.wpTrans] at hwp
    simp [wp, Except.instWP._aux_1, StateT.run, hx, hwp, ExceptT.run, Id.run]

/-- con-leche: none — **the `Std.Do` triple proves the `Std.WP` one**; the
spec side of the bridge, what `@[wp_spec]` and `wp%` apply. -/
theorem AM.wp_of_do {α : Type} {x : AM α} {P : AState → Prop}
    {Q : α → AState → Prop} (h : ⦃fun s => ⌜P s⌝⦄ x ⦃⇓? r s => ⌜Q r s⌝⦄) :
    Std.WP.Triple x P Q (fun _ => True) := by
  constructor
  intro s hs
  have hdo := h s hs
  simp only [Std.WP.StateT.wp_apply_eq, StateT.run]
  cases hx : x s with
  | error e => simp [Std.WP.wp, Std.WP.WP.wpTrans]
  | ok p =>
    simp [wp, Except.instWP._aux_1, StateT.run, hx, ExceptT.run, Id.run] at hdo
    simp [Std.WP.wp, Std.WP.WP.wpTrans, hdo]

/-- con-leche: none — the `Std.WP` twin of a (possibly `∀`-quantified)
`Std.Do` spec proof: `fun xs => AM.wp_of_do (prf xs)`, its `P`/`Q` read off
by unification and beta-reduced. -/
def toWPSpecProof (prf : Expr) : MetaM Expr := do
  let ty ← inferType prf
  forallTelescope ty fun xs _ => do
    let p ← mkAppM ``AM.wp_of_do #[mkAppN prf xs]
    let p ← instantiateMVars p
    -- `vcgen`'s unifier rejects a `let` ("unexpected let-declaration term
    -- during structural definitional equality"), and a structure update
    -- `{ s.memos with … }` in a postcondition elaborates to one
    let pty ← zetaReduce (← instantiateMVars (← inferType p))
    mkLambdaFVars xs (← mkExpectedTypeHint p pty)

/-- con-leche: none — `wp% h`: the `Std.WP` twin of a local `Std.Do` spec,
for `vcgen [wp% h]`. -/
elab "wp% " t:term : term => do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  toWPSpecProof (← instantiateMVars e)

/-- con-leche: none — `@[wp_spec]`: derive `<name>.wp`, the `Std.WP` twin of
a `Std.Do` spec theorem, and file it under `@[spec]` for `vcgen` (at the
priority given, `@[wp_spec high]`, and `local` if asked). -/
initialize registerBuiltinAttribute {
  name := `wp_spec
  descr := "derive the Std.WP twin `<name>.wp` of a Std.Do spec and register it with @[spec]"
  applicationTime := .afterCompilation
  add := fun declName stx kind => do
    let info ← getConstInfo declName
    let wpName := declName ++ `wp
    -- a second `wp_spec` (a `local` re-registration at another priority)
    -- reuses the twin the first one derived
    unless (← getEnv).contains wpName do
      MetaM.run' do
        let prf ← toWPSpecProof (mkConst declName (info.levelParams.map mkLevelParam))
        let ty ← instantiateMVars (← inferType prf)
        addDecl <| .thmDecl {
          name := wpName, levelParams := info.levelParams, type := ty, value := prf }
    -- `spec` reads its priority off `stx[1]`, where `wp_spec`'s own sits
    let some impl := (getAttributeImpl (← getEnv) `spec).toOption
      | throwError "wp_spec: no `spec` attribute"
    impl.add wpName stx kind
}

/-- con-leche: none — **`to_wp`**: the goal side of the bridge.  `apply
AM.do_of_wp`, then zeta-reduce the target: a structure update in a
postcondition is a `let`, which `vcgen`'s unifier rejects. -/
elab "to_wp" : tactic => Tactic.withMainContext do
  Tactic.evalTactic (← `(tactic| apply AM.do_of_wp))
  Tactic.liftMetaTactic1 fun g => do
    g.replaceTargetDefEq (← zetaReduce (← instantiateMVars (← g.getType)))

end ConRon.Bridge
