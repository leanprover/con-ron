import ConRon.Refine.Installed
import ConLeche.MainTheorem

/-! # The capstone: `conron.model_exists` and `conron.no_proof_of_False` (task #60)

`CORE_PLAN.md` **step 8**, and DESIGN.md §1's second and third displayed
theorems.  There is nothing algorithmic here: `Refine/Installed.lean`'s
`check_decls_refines` says that an accept of the Rust `check_decls` is an
accept of con-leche's `checkDecls` at the abstracted inputs and the abstracted
environment, and `ConLeche.model_exists` / `ConLeche.no_proof_of_False`
(`vendor/con-leche/ConLeche/MainTheorem.lean`) say what an accept of
`checkDecls` buys.  This file composes the two, once each.

## What the statements mean

`conron.model_exists V … h : Nonempty (Model V (absEnv e))` — **every
environment the Rust checker accepts has a model in every set theory**, `V`
ranging over any `SetTheory` instance, exactly as con-leche's theorem does.
`conron.no_proof_of_False` is its corollary: an accepted stream never yields a
constant of type `False`.

`absEnv` is `Refine/Abs.lean`'s: `Env.consts` is a list on both sides, stored
reversed in the port (task #50), and the abstraction reverses it back.  So the
environment the theorem is about is the *port's own* environment, read as
con-leche reads it — nothing is re-checked on the Lean side.

## The hypotheses, and who discharges each

Both theorems carry exactly `Refine/Installed.lean`'s four, and no others:

| hypothesis | what it says | who closes it |
|---|---|---|
| `hk : Core.KnotSpec .Verified IndAbs.checkFuelU` | the six core wrappers and bodies refine con-leche's knot at the checker's fuel | task #55 (`Refine/Core/Arms/*`, `Refine/Core/Knot.lean`) |
| `hind : IndRoutesSpec .Verified` | the two inductive install routes refine theirs | task #57 proved `IndRoutesSpecP`; task #59's `ind_routes_spec_of_p` is the bridge to this form |
| `hpins : absPins pins = ConLeche.natOpPinSets` | the `Nat`-op pin list the port threads is the global the pinned con-leche bakes into `checkDeclStepC` | `Refine/Pins.lean`'s `check_decls_pins_refines` for the binary's own list, or the `pins-param` submodule bump, which deletes the hypothesis |
| `hds : ∀ d ∈ ds.val, DeclCWF d` | every parsed term is well formed | the parser: `DeclCWF` is the task-#5 inductive invariant whose constructors *are* the port's smart constructors, so a `DeclC` built by `crates/con-ron/src/frontend` satisfies it by construction |

## The axiom census

The two `#print axioms` blocks below are machine-checked (`#guard_msgs`), and
they are the P3 gate: when task #55, #57's bridge and the pin statements land,
`sorryAx` leaves these two lines and what is left must be *exactly*
`[propext, Classical.choice, Quot.sound]` — con-leche's own three
(`vendor/con-leche/tests/ConLecheTests/Axioms.lean`), and nothing else.

**Nothing here may reach `kernel::pins_text::PINS_TEXT`** (task #43): the
constant's own Lean value is fine, but any closed claim *about* it needs
`decide +native`, whose `Lean.ofReduceBool`/`Lean.trustCompiler` would show up
in this census.  It does not, and the guard is what keeps it that way: `pins`
is a *parameter* of `check_decls` here and `hpins` is a hypothesis about it, so
the embedded text is not in the proof closure at all.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine

open ConRon.Refine.CheckerDecl (absDeclC DeclCWF)
open ConRon.Refine.Installed (leanCheckDecls check_decls_refines)

universe w

/-- **The port's accept is con-leche's accept** (DESIGN.md §1's first displayed
theorem, at `.verified`): `check_decls_refines` with `leanCheckDecls` unfolded,
which is what the two corollaries below feed to con-leche's theorems. -/
theorem check_decls_verified_refines
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ConLeche.Cached.checkDecls .verified (ds.val.map absDeclC) = .ok (absEnv e) := by
  have hr := check_decls_refines hk hind hpins hds h
  rw [leanCheckDecls] at hr
  exact hr

/-- **The main theorem for the Rust checker** (DESIGN.md §1): every environment
`crates/con-ron-core`'s `check_decls` accepts has a model in every set theory.
`ConLeche.model_exists` at the accept above. -/
theorem conron.model_exists (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  ConLeche.model_exists V (ds.val.map absDeclC) (absEnv e)
    (check_decls_verified_refines hk hind hpins hds h)

/-- **The main corollary for the Rust checker** (DESIGN.md §1): an accepted
stream never yields a constant of type `False`.  `ConLeche.no_proof_of_False`
at the same accept. -/
theorem conron.no_proof_of_False (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  ConLeche.no_proof_of_False V (ds.val.map absDeclC) (absEnv e)
    (check_decls_verified_refines hk hind hpins hds h)

/-! ## The census (DESIGN.md §5, the P3 gate)

`sorryAx` is task #55's and the pin statements'; the other three are
con-leche's own.  Nothing native-decide-shaped appears, which is the
`PINS_TEXT` guard of the module note. -/

/-- info: 'ConRon.Refine.conron.model_exists' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists

/-- info: 'ConRon.Refine.conron.no_proof_of_False' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False

-- The upstream theorems this tier composes with, for comparison: con-leche's
-- own census is the three standard axioms and nothing else.

/-- info: 'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.model_exists

/-- info: 'ConLeche.no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.no_proof_of_False

end ConRon.Refine
