import ConRon.Refine.Installed
import ConRon.Refine.PinsWF
import ConRon.Refine.Core.Arms.Arms
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

Both theorems carry exactly `Refine/Installed.lean`'s five, and no others:

| hypothesis | what it says | who closes it |
|---|---|---|
| `hk : Core.KnotSpec .Verified IndAbs.checkFuelU` | the six core wrappers and bodies refine con-leche's knot at the checker's fuel | task #55 (`Refine/Core/Arms/*`, `Refine/Core/Knot.lean`) |
| `hind : IndRoutesSpec .Verified` | the two inductive install routes refine theirs | task #57 proved `IndRoutesSpecP`; task #59's `ind_routes_spec_of_p` is the bridge to this form |
| `hpins : absPins pins = ConLeche.natOpPinSets` | the `Nat`-op pin list the port threads is the global the pinned con-leche bakes into `checkDeclStepC` | `Refine/Pins.lean`'s `check_decls_pins_refines` for the binary's own list, or the `pins-param` submodule bump, which deletes the hypothesis |
| `hvar : CheckerPins.PinsWF pins` | every node of every pin is what the port's own smart constructor built | the same construction argument as `hds`: task #58 added it because `hpins` alone does not give it — two pin lists can abstract to `natOpPinSets` with one carrying a stored hash word that makes `expr::beq` inexact |
| `hds : ∀ d ∈ ds.val, DeclCWF d` | every parsed term is well formed | the parser: `DeclCWF` is the task-#5 inductive invariant whose constructors *are* the port's smart constructors, so a `DeclC` built by `crates/con-ron/src/frontend` satisfies it by construction |

## The axiom census

The two `#print axioms` blocks below are machine-checked (`#guard_msgs`), and
they are the P3 gate: `sorryAx` was to leave these two lines and what is left
be *exactly* `[propext, Classical.choice, Quot.sound]` — con-leche's own three
(`vendor/con-leche/tests/ConLecheTests/Axioms.lean`), and nothing else.  **It
did, at task #58**; the knot, the routes and the pins stayed *hypotheses*
rather than becoming axioms, which is the point.

**The two `pins`-parametric theorems may not reach `kernel::pins_text::
PINS_TEXT`** (task #43), and do not: `pins` is a *parameter* of `check_decls`
there and `hpins` is a hypothesis about it, so the embedded text is not in
their proof closure at all, and no native evaluation is either.  That is the
whole point of keeping them alongside the `*_embedded` corollaries task #64
added below, which *do* name the embedded constant and therefore carry the two
native-decide axioms `Refine/Pins.lean`'s `pins_closed` spends.  Both censuses
are pinned; the difference between them is the trust story, and
`Refine/README.md` spells it out.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine

open ConRon.Refine.CheckerDecl (absDeclC DeclCWF)
open ConRon.Refine.Installed (leanCheckDecls check_decls_refines)

universe w

/-- **The port's verdict is con-leche's verdict** (DESIGN.md §1's first
displayed theorem, at `.verified`): `check_decls_refines` with `leanCheckDecls`
unfolded, over the **whole** outcome (task #67's ruling) — the same environment
on an accept, and on a mirrored reject the same error kind at the same position
in the stream.  The port's own `Native` claims nothing (`ErrSimPos`).  The two
corollaries below feed the accept half to con-leche's theorems. -/
theorem check_decls_verified_refines
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC}
    {out : core.result.Result env.Env (core_types.CheckError × Std.U64)}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok out) :
    match out with
    | .Ok e => ConLeche.Cached.checkDecls .verified (ds.val.map absDeclC) = .ok (absEnv e)
    | .Err er =>
      Installed.ErrSimPos er (ConLeche.Cached.checkDecls .verified (ds.val.map absDeclC)) := by
  have hr := check_decls_refines hk hind hinde hvar hpins hds h
  rw [leanCheckDecls] at hr
  cases out with
  | Ok e => exact hr
  | Err er => exact hr

/-- `check_decls_verified_refines` at an accept, the pre-#67 statement — what
the two capstones below consume. -/
theorem check_decls_verified_refines_ok
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ConLeche.Cached.checkDecls .verified (ds.val.map absDeclC) = .ok (absEnv e) :=
  check_decls_verified_refines hk hind hinde hvar hpins hds h

/-- **The main theorem for the Rust checker** (DESIGN.md §1): every environment
`crates/con-ron-core`'s `check_decls` accepts has a model in every set theory.
`ConLeche.model_exists` at the accept above. -/
theorem conron.model_exists (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  ConLeche.model_exists V (ds.val.map absDeclC) (absEnv e)
    (check_decls_verified_refines_ok hk hind hinde hvar hpins hds h)

/-- **The main corollary for the Rust checker** (DESIGN.md §1): an accepted
stream never yields a constant of type `False`.  `ConLeche.no_proof_of_False`
at the same accept. -/
theorem conron.no_proof_of_False (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  ConLeche.no_proof_of_False V (ds.val.map absDeclC) (absEnv e)
    (check_decls_verified_refines_ok hk hind hinde hvar hpins hds h)

/-! ## The knot discharged

`Core.knot_spec` (task #61) proves `KnotSpec mode fuel` at every fuel, so `hk`
is not a hypothesis of the theorems below; the three that remain are named in
`Refine/README.md` with their owners (`hind`: task #59; `hpins`/`hvar`: task
#64).  Task #58's `hoe` is gone: task #65 made a thrown pin attempt the pin
check's verdict, retiring both halves of the `orElse` deviation (DESIGN.md
§3). -/

theorem conron.model_exists' (V : Type w) [ConLeche.SetTheory V]
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists V (Core.knot_spec IndAbs.checkFuelU) hind hinde hvar hpins hds h

theorem conron.no_proof_of_False' (V : Type w) [ConLeche.SetTheory V]
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False V (Core.knot_spec IndAbs.checkFuelU) hind hinde hvar hpins hds h

/-- info: 'ConRon.Refine.conron.model_exists'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists'

/-- info: 'ConRon.Refine.conron.no_proof_of_False'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False'

/-! ## The instance at the binary's own pins (task #64)

The theorems above are general in `pins` and carry
`hpins : absPins pins = ConLeche.natOpPinSets` — a promise about an argument
the binary was *given*.  For a real run the argument is not free:
`con_ron::driver::pins_for_run` hands `check_decls` the **verified** decoder
applied to the embedded `con-ron-pins/1` constant, and `Refine/Pins.lean`'s
`check_decls_pins_refines` says what that equals.  The two corollaries below
are `conron.model_exists'` / `conron.no_proof_of_False'` with `hpins`
discharged that way, for the pin list the binary actually folds with — so
they carry neither `hk` (`Core.knot_spec`, task #61) nor `hpins`.

**Both versions are kept, and the difference between them is the trust
story.**  The primed theorems do not mention the embedded text at all, so
nothing native-decide-shaped is in their closure and their census is
con-leche's own three axioms.  These two inherit exactly two more, both
native evaluation on *static data*: `pins_closed`'s sealed axiom, which
asserts that the embedded text decodes to con-leche's `natOpPinSets`, and the
one Aeneas's `toStr` already spends on every extracted `&str` constant.  Both
censuses are pinned below; `Refine/README.md`'s "Where the native-decide
axiom lives" is the standing statement of what that buys, and DESIGN.md §3
records that spike #63 measured the alternatives and that the interim stands.

`hvar : CheckerPins.PinsWF pins` is **not** discharged here and is task #64's
one piece of owed work: it needs `ExprWF` for every expression the decoder
installs, i.e. a full well-formedness invariant threaded through
`Refine/PinsBytes.lean` and `Refine/PinsRecords.lean` — cheap in kind, since
`ExprWF`'s constructors *are* the port's smart constructors and every record
already applies one, but a contract change across the whole of half (A).
DESIGN.md's task #64 entry has the recipe. -/

/-- **The main theorem for the shipped binary** (task #64): the same
statement as `conron.model_exists'`, for the pin list
`con_ron::driver::pins_for_run` passes by default —
`kernel::pins_decode::decode_embedded()`, the verified decoder on the
embedded text — and therefore with no hypothesis about the pins' *value*. -/
theorem conron.model_exists_embedded (V : Type w) [ConLeche.SetTheory V]
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists' V hind hinde (PinsWF.decode_embedded_wf hp)
    (check_decls_pins_refines_ok pins hp) hds h

/-- **The main corollary for the shipped binary** (task #64):
`conron.no_proof_of_False'` at the embedded pins. -/
theorem conron.no_proof_of_False_embedded (V : Type w) [ConLeche.SetTheory V]
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False' V hind hinde (PinsWF.decode_embedded_wf hp)
    (check_decls_pins_refines_ok pins hp) hds h

/-! ## The census (DESIGN.md §5, the P3 gate) — **passed**

`sorryAx` is **gone** (task #58 closed the last door, `checkDeclStepC`'s
declaration arms).  The two main theorems now depend on exactly con-leche's own
three axioms and nothing else, which is what the note above said this gate
would look like when it flipped.  Nothing native-decide-shaped appears, which
is the `PINS_TEXT` guard of the module note.

What remains is *hypotheses*, which are not axioms and are listed in the table
above with who closes each: `hk` (task #55's knot, proved at #61 but not yet
plugged in here), `hind`, `hpins` and `hvar`. -/

/-- info: 'ConRon.Refine.conron.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists

/-- info: 'ConRon.Refine.conron.no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False

-- The upstream theorems this tier composes with, for comparison: con-leche's
-- own census is the three standard axioms and nothing else.

/-- info: 'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.model_exists

/-- info: 'ConLeche.no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.no_proof_of_False

-- The binary-instance corollaries (task #64).  Two entries more than the
-- general theorems above, and exactly two: `pins_closed`'s own sealed
-- native-evaluation axiom (Lean 4.33 seals `native_decide` into a fresh axiom
-- named after the theorem, asserting `decide P = true` and nothing else,
-- rather than emitting `Lean.ofReduceBool`), and the one Aeneas's `toStr`
-- spends on every extracted `&str` constant.  Nothing else changes.

/-- info: 'ConRon.Refine.conron.model_exists_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 pins_closed._native.native_decide.ax_1_2,
 pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms conron.model_exists_embedded

/-- info: 'ConRon.Refine.conron.no_proof_of_False_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 pins_closed._native.native_decide.ax_1_2,
 pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms conron.no_proof_of_False_embedded

end ConRon.Refine
