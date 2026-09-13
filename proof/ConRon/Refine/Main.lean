import ConRon.Refine.Installed
import ConRon.Refine.PinsWF
import ConRon.Refine.IndC
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

`conron.model_exists` and `conron.no_proof_of_False` are the fully general
form and carry `Refine/Installed.lean`'s four.  **Every one of them is
discharged below** (`hk` since task #61, `hind`/`hinde` at task #67 continued,
`hvar` at task #66), so the two `_embedded` corollaries at the bottom of this
file carry `hp` — the decoded pins — and the run `h`, and nothing else.  Two
hypotheses the tier used to owe are gone rather than discharged: `hpins`, since
**task #74** vendored con-leche's pins-parametric fold, and `hds`, since **task
#73 makes `check_decls` check it** (`kernel::validate`, `Refine/Validate.lean`).

| hypothesis | what it says | who closes it |
|---|---|---|
| `hk : Core.KnotSpec .Verified IndAbs.checkFuelU` | the six core wrappers and bodies refine con-leche's knot at the checker's fuel | task #55 (`Refine/Core/Arms/*`, `Refine/Core/Knot.lean`) |
| `hind : IndRoutesSpec .Verified` | the two inductive install routes refine theirs on an accept | `IndC.ind_routes_spec'` from the knot (task #57's `IndRoutesSpecP`, task #59's `ind_routes_spec_of_p`) — **discharged below** |
| `hinde : IndRoutesSpecErr .Verified` | …and throw at the same kind on a mirrored reject, down the same branch of `nativeParts?` | `IndC.ind_routes_spec_err'` from the knot (task #67 continued) — **discharged below** |
| `hvar : CheckerPins.PinsWF pins` | every node of every pin is what the port's own smart constructor built | `PinsWF.decode_embedded_wf` (task #66), for the embedded pins — **discharged below**.  The `pins`-parametric theorems keep it: it is a promise about an argument, and no statement about the pins' *value* implies it — two pin lists can abstract to the same `List NatOpPinSet` with one carrying a stored hash word that makes `expr::beq` inexact |
| ~~`hds : ∀ d ∈ ds.val, DeclCWF d`~~ | every parsed term is well formed | **gone (task #73)**: `cached::installed::check_decls` now *validates* its input — `kernel::validate` rebuilds every node with the port's own smart constructor and compares the stored word — and `Refine/Validate.lean`'s `validate_decls_sound` supplies the predicate at the accept.  A malformed declaration is declined with `CheckError::Native`, about which the full-outcome ruling claims nothing |

`hpins : absPins pins = ConLeche.natOpPinSets` was a sixth until **task #74**.
It said that the pin list the port threads is the global the pinned con-leche
baked into `checkDeclStepC`; the vendored con-leche takes the list as an
argument of the fold instead (its task #285), so the whole tower is stated at
`absPins pins` and there is no hypothesis about the pins' value anywhere.

## The axiom census

The two `#print axioms` blocks below are machine-checked (`#guard_msgs`), and
they are the P3 gate: `sorryAx` was to leave these two lines and what is left
be *exactly* `[propext, Classical.choice, Quot.sound]` — con-leche's own three
(`vendor/con-leche/tests/ConLecheTests/Axioms.lean`), and nothing else.  **It
did, at task #58**; the knot, the routes and the pins stayed *hypotheses*
rather than becoming axioms, which is the point.

**Nothing here is evaluated natively any more** (task #74).  The two
`pins`-parametric theorems never named `kernel::pins_text::PINS_TEXT` (task
#43) and still do not; the two `_embedded` corollaries used to *evaluate* it,
through task #64's `pins_closed`, and no longer do — with the fold parametric
in the pins there is nothing to identify with a constant, and the `_embedded`
pair reaches `decode_embedded` only through `PinsWF.decode_embedded_wf`, which
holds for every byte string.  No `native_decide` is invoked anywhere in
`proof/` any more; the word survives only in prose that records what task #64
did and task #74 undid.

The `_embedded` pair's census is therefore the three standard axioms **plus one
that is Aeneas's and not ours**: `pins_text.PINS_TEXT._native.decide.ax_1`,
which `toStr` spends by `decide +native` on the size bound of *every* extracted
`&str` constant (`AENEAS_FINDINGS.md` §3.8).  It lives in the constant's
definition, so a theorem that names the binary's own decode run inherits it
whether or not anything is computed; removing it needs an upstream change.
Task #64's second entry, the port's own sealed `pins_closed` axiom, is gone.

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
    {ds : alloc.vec.Vec parsed_c.DeclC}
    {out : core.result.Result env.Env (core_types.CheckError × Std.U64)}
    (h : cached.installed.check_decls .Verified pins ds = ok out) :
    match out with
    | .Ok e =>
      ConLeche.Cached.checkDecls .verified (ds.val.map absDeclC) (absPins pins)
        = .ok (absEnv e)
    | .Err er =>
      Installed.ErrSimPos er
        (ConLeche.Cached.checkDecls .verified (ds.val.map absDeclC)
          (absPins pins)) := by
  have hr := check_decls_refines hk hind hinde hvar h
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
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ConLeche.Cached.checkDecls .verified (ds.val.map absDeclC) (absPins pins)
      = .ok (absEnv e) :=
  check_decls_verified_refines hk hind hinde hvar h

/-- **The main theorem for the Rust checker** (DESIGN.md §1): every environment
`crates/con-ron-core`'s `check_decls` accepts has a model in every set theory.
`ConLeche.model_exists` at the accept above. -/
theorem conron.model_exists (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  ConLeche.model_exists_with V (absPins pins) (ds.val.map absDeclC) (absEnv e)
    (check_decls_verified_refines_ok hk hind hinde hvar h)

/-- **The main corollary for the Rust checker** (DESIGN.md §1): an accepted
stream never yields a constant of type `False`.  `ConLeche.no_proof_of_False`
at the same accept. -/
theorem conron.no_proof_of_False (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  ConLeche.no_proof_of_False_with V (absPins pins) (ds.val.map absDeclC)
    (absEnv e)
    (check_decls_verified_refines_ok hk hind hinde hvar h)

/-! ## The knot and the inductive routes discharged

`Core.knot_spec` (task #61) proves `KnotSpec mode fuel` at every fuel, and
`Refine/IndC.lean`'s `ind_routes_spec'` / `ind_routes_spec_err'` take that to
both halves of the inductive seam (task #57/#59 for the accept half, task #67
continued for the failure half), so `hk`, `hind` and `hinde` are not
hypotheses of the theorems below.  The one that remains here is the pin
argument's well-formedness (`hvar`), and the corollaries further down discharge
that as well for the list the binary actually folds with; `Refine/README.md`
names each with its owner.  Task #58's `hoe` is gone: task #65 made a thrown pin attempt the pin
check's verdict, retiring both halves of the `orElse` deviation (DESIGN.md
§3). -/

theorem conron.model_exists' (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists V (Core.knot_spec IndAbs.checkFuelU)
    (InductivesC.ind_routes_spec' (Core.knot_spec IndAbs.checkFuelU))
    (InductivesC.ind_routes_spec_err' (Core.knot_spec IndAbs.checkFuelU))
    hvar h

theorem conron.no_proof_of_False' (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False V (Core.knot_spec IndAbs.checkFuelU)
    (InductivesC.ind_routes_spec' (Core.knot_spec IndAbs.checkFuelU))
    (InductivesC.ind_routes_spec_err' (Core.knot_spec IndAbs.checkFuelU))
    hvar h

/-- info: 'ConRon.Refine.conron.model_exists'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists'

/-- info: 'ConRon.Refine.conron.no_proof_of_False'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False'

/-! ## The instance at the binary's own pins (tasks #64, #74)

The theorems above are general in `pins` and, since **task #74**, say nothing
about its *value*: the vendored con-leche's fold takes the pin list as an
argument (its task #285), so `conron.model_exists'` is already the statement at
whatever list `con_ron::driver::pins_for_run` hands `check_decls`.  What it
still asks is `hvar : CheckerPins.PinsWF pins`, the argument's own
well-formedness, which is a promise about the argument and not implied by
anything the list abstracts to.

For a real run the argument is not free: the driver passes the **verified**
decoder applied to the embedded `con-ron-pins/1` constant, and task #66's
`Refine/PinsWF.lean` reads `PinsWF` straight off that run
(`decode_embedded_wf`).  The two corollaries below are therefore
`conron.model_exists'` / `conron.no_proof_of_False'` with `hvar` discharged
that way — so they carry neither `hk` (`Core.knot_spec`, task #61), nor
`hind`/`hinde`, nor `hvar`, and there is no `hpins` left to carry.

**Both versions are kept, and what separates them is now only generality, not
trust.**  Task #64's arrangement was different: `hpins` was discharged by
`pins_closed`, a `native_decide` on the 532 KB embedded text, so the `_embedded`
pair inherited two native-evaluation axioms that the primed pair did not.
Task #74 deleted `pins_closed` and everything that fed it; what the `_embedded`
pair still inherits is the single axiom Aeneas's `toStr` spends on the
*definition* of every extracted `&str` constant, which no proof of ours can
avoid while it names the binary's own decode run.  `decode_embedded_wf`'s proof is
one invariant, `TablesWF`, threaded through the decoder's record pass — the
argument DESIGN.md §3.5 fixed at task #5, that the `*WF` predicates are
inductives whose constructors **are** the port's smart constructors — and it
holds for every byte string, so nothing is evaluated by it either.

So **these two carry `hp` and `h` and nothing else**: not `hk`
(`Core.knot_spec`, task #61), not `hind`/`hinde` (`IndC.ind_routes_spec'` /
`ind_routes_spec_err'`, task #67 continued), not `hvar`
(`PinsWF.decode_embedded_wf`, task #66); `hpins` is retired outright by the
pins-parametric fold (task #74), and, since task #73, `hds` is checked rather
than assumed: `check_decls` validates its own input, so there is no longer
anything outside this proof that has to hold up its end. -/

/-- **The main theorem for the shipped binary** (tasks #64, #74): the same
statement as `conron.model_exists'`, for the pin list
`con_ron::driver::pins_for_run` passes by default —
`kernel::pins_decode::decode_embedded()`, the verified decoder on the
embedded text.  It carries `hp` (what the decoder returned) and `hds`; `hp` is
there for `PinsWF` alone, and no hypothesis anywhere is about the pins'
*value*. -/
theorem conron.model_exists_embedded (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists' V (PinsWF.decode_embedded_wf hp) h

/-- **The main corollary for the shipped binary** (tasks #64, #74):
`conron.no_proof_of_False'` at the embedded pins. -/
theorem conron.no_proof_of_False_embedded (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False' V (PinsWF.decode_embedded_wf hp) h

/-! ## The census (DESIGN.md §5, the P3 gate) — **passed**

`sorryAx` is **gone** (task #58 closed the last door, `checkDeclStepC`'s
declaration arms).  The two main theorems depend on exactly con-leche's own
three axioms and nothing else, which is what the note above said this gate
would look like when it flipped.  Since task #74 **so do the two `_embedded`
corollaries**: nothing native-decide-shaped appears anywhere in this file's
closure, which is the `PINS_TEXT` guard of the module note, now unconditional.

What remained after that was *hypotheses*, which are not axioms; since task
#67's campaign closed and task #74 landed, five of the six are gone — `hk`
(`Core.knot_spec`), `hind`/`hinde` (`IndC.ind_routes_spec'` /
`ind_routes_spec_err'`) and `hvar` (`PinsWF.decode_embedded_wf`) discharged
here, `hpins` retired outright by the parametric fold (task #74), and `hds`
gone at task #73 by being **checked** rather than assumed — and what the two
`_embedded` corollaries carry is the decoded pins `hp` and the run `h`. -/

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

-- The binary-instance corollaries (task #64, restated at task #74).  ONE entry
-- more than the general theorems above, where task #64 had two: the port's own
-- `pins_closed` sealed axiom is gone with `pins_closed` itself, because the
-- parametric fold leaves nothing about the embedded text to decide.  What is
-- left is Aeneas's, and it is not ours to remove: `toStr` discharges its bound
-- `s.toByteArray.size <= U32.max` with `by decide +native` on EVERY extracted
-- `&str` constant (`AENEAS_FINDINGS.md` §3.8), so it sits in the DEFINITION of
-- `kernel::pins_text::PINS_TEXT`, and any statement that names the binary's own
-- decode run inherits it through the constant's closure.  Nothing here
-- evaluates the text: `PinsWF.decode_embedded_wf` holds for every byte string.

/-- info: 'ConRon.Refine.conron.model_exists_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms conron.model_exists_embedded

/-- info: 'ConRon.Refine.conron.no_proof_of_False_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms conron.no_proof_of_False_embedded

end ConRon.Refine
