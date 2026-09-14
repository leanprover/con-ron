import ConRon.Refine.Installed
import ConRon.Refine.PinsWF
import ConRon.Refine.IndC
import ConRon.Refine.Core.Arms.Arms
import ConRon.Refine.BasisRaw
import ConRon.Refine.Frontend.Chunks
import ConRon.Refine.Frontend.Prepare
import ConRon.Refine.Frontend.ChunksR
import ConRon.Refine.Frontend.PrepareR
import ConLeche.MainTheorem

/-! # The capstone: `conron.model_exists` and `conron.no_proof_of_False` (task #60)

`CORE_PLAN.md` **step 8**, and DESIGN.md §1's second and third displayed
theorems.  There is nothing algorithmic here: `Refine/Installed.lean`'s
`check_decls_refines` says that an accept of the Rust `check_decls` is an
accept of con-leche's `checkDecls` at the abstracted inputs and the abstracted
environment, and `ConLeche.model_exists` /
`ConLeche.Cached.no_proof_of_False_cached`
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
form and carry `Refine/Installed.lean`'s five.  **Every one of them but `hds`
is discharged below** (`hk` since task #61, `hind`/`hinde` at task #67
continued, `hvar` at task #66), so the two `_embedded` corollaries at the
bottom of this file carry `hp` — the decoded pins — the input's
well-formedness `hds`, and the run `h`.  One hypothesis the tier used to owe
is gone rather than discharged: `hpins`, since **task #74** vendored
con-leche's pins-parametric fold.  `hds` was checked rather than assumed
between tasks #73 and #81; **task #81 withdrew that runtime check** because it
cost 10 GB of resident memory at Mathlib scale and 4 % of the instructions.

**Since task #85 `hds` is discharged too, one level up.**  Task #84 put the
parser into the verified core and task #85 proved every declaration it produces
well formed (`Refine/Frontend/`), so the chunk-level pair at the bottom of this
file — `conron.model_exists_parsed` / `conron.no_proof_of_False_parsed`, the
statement about con-leche's whole four-step pipeline — carries **no**
well-formedness hypothesis at all.  What stands in its place is one line about
the **modeller** (`hgen : Frontend.ModellerWF inst g`), the residue task #84's
seam left and the maintainer accepted.  The four theorems above keep `hds`: they
are about the fold alone, and a caller who does not go through the port's parser
still owes it.

| hypothesis | what it says | who closes it |
|---|---|---|
| `hk : Core.KnotSpec .Verified IndAbs.checkFuelU` | the six core wrappers and bodies refine con-leche's knot at the checker's fuel | task #55 (`Refine/Core/Arms/*`, `Refine/Core/Knot.lean`) |
| `hind : IndRoutesSpec .Verified` | the two inductive install routes refine theirs on an accept | `IndC.ind_routes_spec'` from the knot (task #57's `IndRoutesSpecP`, task #59's `ind_routes_spec_of_p`) — **discharged below** |
| `hinde : IndRoutesSpecErr .Verified` | …and throw at the same kind on a mirrored reject, down the same branch of `nativeParts?` | `IndC.ind_routes_spec_err'` from the knot (task #67 continued) — **discharged below** |
| `hvar : CheckerPins.PinsWF pins` | every node of every pin is what the port's own smart constructor built | `PinsWF.decode_embedded_wf` (task #66), for the embedded pins — **discharged below**.  The `pins`-parametric theorems keep it: it is a promise about an argument, and no statement about the pins' *value* implies it — two pin lists can abstract to the same `List NatOpPinSet` with one carrying a stored hash word that makes `expr::beq` inexact |
| `hds : ∀ d ∈ ds.val, DeclarationWF d` | every parsed term is well formed | **task #85** (`Frontend.parse_chunks_wf` and `Frontend.prepare_prelude_wf`), for input the port's own parser produced — `DeclarationWF` is the task-#5 inductive invariant whose constructors *are* the port's smart constructors, so the parse satisfies it by construction and the proof is that argument written out.  Task #73 discharged it with a runtime validation pass and **task #81 withdrew that pass** (it cost 10 GB at Mathlib scale).  **Discharged at the chunk-level pair at the bottom of this file**; the four theorems above keep it, since they are about the fold alone |

`hpins : absPins pins = ConLeche.natOpPinSets` was a sixth until **task #74**.
It said that the pin list the port threads is the global the pinned con-leche
baked into `checkDeclStepC`; the vendored con-leche takes the list as an
argument of the fold instead (its task #304, on upstream master since task #83's
bump: `pins` is `checkDecls`' explicit second argument with no default), so the
whole tower is stated at `absPins pins` and there is no hypothesis about the
pins' value anywhere.  The same bump retired `ConLeche.model_exists_with` /
`no_proof_of_False_with`: there is one pair of upstream theorems now, and it is
already over every pin list, so this file composes with that pair directly.

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

**The chunk-level pair paid sixty-eight more of that artifact until task #86**,
and its own section below says why: `frontend::scan_fast::key_at` recognised
the dialect's object keys against a table of 66 `&str` constants and
`scan_bool` against two more, so any statement that named `parse_chunks`
inherited their `toStr` axioms through the closure with nothing evaluated.
Task #86 spelled all 68 as `[u8; N]` byte arrays — F17's route, already forced
on seven literals of the same module — so the pair is pinned at the standard
three, and `PINS_TEXT` is the port's last `&str` constant.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine

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
    (hraw : CheckerDecl.BasisRawSpec)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec env.Declaration}
    {out : core.result.Result env.Env (core_types.CheckError × Std.U64)}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok out) :
    match out with
    | .Ok e =>
      ConLeche.Cached.checkDecls .verified (absPins pins)
        ⟨ds.val.map absDeclaration⟩ = .ok (absEnv e)
    | .Err er =>
      Installed.ErrSimPos er
        (ConLeche.Cached.checkDecls .verified (absPins pins)
          ⟨ds.val.map absDeclaration⟩) := by
  have hr := check_decls_refines hk hraw hind hinde hvar hds h
  rw [leanCheckDecls] at hr
  cases out with
  | Ok e => exact hr
  | Err er => exact hr

/-- `check_decls_verified_refines` at an accept, the pre-#67 statement — what
the two capstones below consume. -/
theorem check_decls_verified_refines_ok
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hraw : CheckerDecl.BasisRawSpec)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ConLeche.Cached.checkDecls .verified (absPins pins)
      ⟨ds.val.map absDeclaration⟩ = .ok (absEnv e) :=
  check_decls_verified_refines hk hraw hind hinde hvar hds h

/-- **The main theorem for the Rust checker** (DESIGN.md §1): every environment
`crates/con-ron-core`'s `check_decls` accepts has a model in every set theory.
`ConLeche.model_exists` at the accept above. -/
theorem conron.model_exists (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hraw : CheckerDecl.BasisRawSpec)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  ConLeche.model_exists V (absPins pins) ⟨ds.val.map absDeclaration⟩ (absEnv e)
    (check_decls_verified_refines_ok hk hraw hind hinde hvar hds h)

/-- **The main corollary for the Rust checker** (DESIGN.md §1): an accepted
stream never yields a constant of type `False`.  con-leche's
`Cached.no_proof_of_False_cached` — the fold's own letter about `False`, which
is what survived con-leche's task #291 at the environment — at the same
accept.  The *chunk*-level corollary, `ConLeche.no_False_declaration`, is about
the whole pipeline including the parser, and is con-ron's task #84. -/
theorem conron.no_proof_of_False (V : Type w) [ConLeche.SetTheory V]
    (hk : Core.KnotSpec .Verified IndAbs.checkFuelU)
    (hraw : CheckerDecl.BasisRawSpec)
    (hind : IndRoutesSpec .Verified) (hinde : IndRoutesSpecErr .Verified)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  fun hc =>
    let ⟨c, hmem, hty⟩ := hc
    ConLeche.Cached.no_proof_of_False_cached V (μ := .verified) rfl
      (check_decls_verified_refines_ok hk hraw hind hinde hvar hds h) c hmem hty

/-! ## The pin recogniser discharged

`Refine/BasisRaw.lean` and `Refine/Canon.lean` prove the four facts
`CheckerDecl.BasisRawSpec` bundles — con-leche's task #293 moved the
pinned-block match out of the parser into the fold, so `checkDecl` reads
`basisPinHit`, `quotPinHit`, `quotBasis` and `ConstantInfo.canonEq`, and the
port's counterparts refine them.  The bundle is stated in `CheckerDecl.lean`,
in the `IndRoutesSpec` idiom, because that is where the arms consume it; the
witness is here, beside the knot's, because this is where the tower's
hypotheses are discharged. -/

/-- **The pin recogniser refines con-leche's** (con-leche task #293). -/
theorem conron.basis_raw_spec : CheckerDecl.BasisRawSpec where
  basisPinHit := fun hblock h => BasisRaw.basis_pin_hit_refines hblock h
  quotPinHit := fun hcv h => BasisRaw.quot_pin_hit_refines hcv h
  quotBasisAt := fun h => BasisRaw.quot_basis_at_refines h
  constantInfoCanonEq := fun ha hb h => Canon.constant_info_canon_eq_refines ha hb h

/-! ## The knot and the inductive routes discharged

`Core.knot_spec` (task #61) proves `KnotSpec mode fuel` at every fuel, and
`Refine/IndC.lean`'s `ind_routes_spec'` / `ind_routes_spec_err'` take that to
both halves of the inductive seam (task #57/#59 for the accept half, task #67
continued for the failure half); `conron.basis_raw_spec` just above proves the
pin recogniser's four facts (task #83).  So `hk`, `hraw`, `hind` and `hinde`
are not hypotheses of the theorems below.  The one that remains here is the pin
argument's well-formedness (`hvar`), and the corollaries further down discharge
that as well for the list the binary actually folds with; `Refine/README.md`
names each with its owner.  Task #58's `hoe` is gone: task #65 made a thrown pin attempt the pin
check's verdict, retiring both halves of the `orElse` deviation (DESIGN.md
§3). -/

theorem conron.model_exists' (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists V (Core.knot_spec IndAbs.checkFuelU) conron.basis_raw_spec
    (InductivesC.ind_routes_spec' (Core.knot_spec IndAbs.checkFuelU))
    (InductivesC.ind_routes_spec_err' (Core.knot_spec IndAbs.checkFuelU))
    hvar hds h

theorem conron.no_proof_of_False' (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False V (Core.knot_spec IndAbs.checkFuelU) conron.basis_raw_spec
    (InductivesC.ind_routes_spec' (Core.knot_spec IndAbs.checkFuelU))
    (InductivesC.ind_routes_spec_err' (Core.knot_spec IndAbs.checkFuelU))
    hvar hds h

/-- info: 'ConRon.Refine.conron.model_exists'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists'

/-- info: 'ConRon.Refine.conron.no_proof_of_False'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False'

/-! ## The headline: the pins the verified decoder produced (task #75)

`hvar` is a promise about the pin *argument*, and the one place a real run gets
it from is the decoder: `con_ron::driver::pins_for_run` calls
`kernel::pins_decode::decode_embedded()`, and task #66's `PinsWF.decode_wf`
reads `PinsWF` off **any** successful decode run — the input is a `Slice U8`
like any other, and nothing about its value is used.  So the pair below is the
statement about *the binary's checker fed the pins its own verified decoder
produced*, with no hypothesis left but that decode and the run itself, and it
names no string constant: its census is con-leche's own three axioms.

The two `_embedded` corollaries in the next section are this pair's instance at
`text = core.str.Str.as_bytes kernel.pins_text.PINS_TEXT` — `decode_embedded`
is that `as_bytes` followed by `decode`, which is what `decode_embedded_wf`
peels — and they pay one axiom for naming the constant (`AENEAS_FINDINGS.md`
§3.8).  They are kept as they are: the extra generality here is exactly the
step that drops the axiom, and both statements are worth having side by side. -/

/-- **The main theorem for the shipped binary, axiom-free** (task #75): every
environment `crates/con-ron-core`'s `check_decls` accepts, when fed a pin list
that `kernel::pins_decode::decode` returned for *some* byte slice, has a model
in every set theory.  `conron.model_exists'` with `hvar` discharged by
`PinsWF.decode_wf`, so it carries `hp` (a decode run), `hds` (the parsed
input's well-formedness) and `h` (the check run), and its census is
con-leche's own three axioms.

This is the theorem about the binary that ships, up to one fact that lives in
the unverified crate and not in this tower: that the driver
(`con_ron::driver::pins_for_run`) calls the decoder on the embedded
`con-ron-pins/1` text rather than on something else.
`conron.model_exists_embedded` below is this theorem at exactly that text. -/
theorem conron.model_exists_decoded (V : Type w) [ConLeche.SetTheory V]
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists' V (PinsWF.decode_wf hp) hds h

/-- **The main corollary for the shipped binary, axiom-free** (task #75): at
decoded pins, an accepted stream never yields a constant of type `False`.
`conron.no_proof_of_False'` with `hvar` discharged by `PinsWF.decode_wf`; like
`conron.model_exists_decoded` it carries the decode run and the check run and
nothing else, and names no string constant, so its census is the three
standard axioms. -/
theorem conron.no_proof_of_False_decoded (V : Type w) [ConLeche.SetTheory V]
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False' V (PinsWF.decode_wf hp) hds h

/-- info: 'ConRon.Refine.conron.model_exists_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists_decoded

/-- info: 'ConRon.Refine.conron.no_proof_of_False_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False_decoded

/-! ## The instance at the binary's own pins (tasks #64, #74)

The theorems above are general in `pins` and, since **task #74**, say nothing
about its *value*: the vendored con-leche's fold takes the pin list as an
argument (its task #304, upstream on master), so `conron.model_exists'` is
already the statement at
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

So **these two carry `hp`, `hds` and `h`**: not `hk`
(`Core.knot_spec`, task #61), not `hind`/`hinde` (`IndC.ind_routes_spec'` /
`ind_routes_spec_err'`, task #67 continued), not `hvar`
(`PinsWF.decode_embedded_wf`, task #66); `hpins` is retired outright by the
pins-parametric fold (task #74).  `hds` is the parser's own invariant, by
construction, and — since task #81 withdrew task #73's runtime check of it —
the one place where something outside this proof has to hold up its end. -/

/-- **The main theorem for the shipped binary** (tasks #64, #74): the same
statement as `conron.model_exists'`, for the pin list
`con_ron::driver::pins_for_run` passes by default —
`kernel::pins_decode::decode_embedded()`, the verified decoder on the
embedded text.  It carries `hp` (what the decoder returned) and `hds` (the
parser's invariant); `hp` is there for `PinsWF` alone, and no hypothesis
anywhere is about the pins' *value*.

It is the **instance of `conron.model_exists_decoded`** (task #75) at
`text = core.str.Str.as_bytes kernel.pins_text.PINS_TEXT`, which is what
`decode_embedded` is, and the one axiom it carries beyond the standard three is
the price of naming that constant: Aeneas's `toStr` discharges its size bound
with `by decide +native` in the *definition* of every extracted `&str`
(`AENEAS_FINDINGS.md` §3.8), so `pins_text.PINS_TEXT._native.decide.ax_1` comes
in through the closure with nothing evaluated.  The **axiom-free headline** is
therefore `conron.model_exists_decoded`, which says the same thing for every
decoder input. -/
theorem conron.model_exists_embedded (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists' V (PinsWF.decode_embedded_wf hp) hds h

/-- **The main corollary for the shipped binary** (tasks #64, #74):
`conron.no_proof_of_False'` at the embedded pins — equivalently, the instance
of `conron.no_proof_of_False_decoded` (task #75) at
`text = core.str.Str.as_bytes kernel.pins_text.PINS_TEXT`.  Its fourth axiom is
Aeneas's `toStr` artifact on the `&str` constant's definition
(`AENEAS_FINDINGS.md` §3.8), not anything this proof evaluates; the axiom-free
headline is the decoded corollary. -/
theorem conron.no_proof_of_False_embedded (V : Type w) [ConLeche.SetTheory V]
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ds : alloc.vec.Vec env.Declaration} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False' V (PinsWF.decode_embedded_wf hp) hds h

/-! ## The census (DESIGN.md §5, the P3 gate) — **passed**

`sorryAx` is **gone** (task #58 closed the last door, `checkDeclStepC`'s
declaration arms).  The two main theorems depend on exactly con-leche's own
three axioms and nothing else, which is what the note above said this gate
would look like when it flipped.  Since task #74 **so do the two `_embedded`
corollaries**: nothing native-decide-shaped appears anywhere in this file's
closure, which is the `PINS_TEXT` guard of the module note, now unconditional.

What remained after that was *hypotheses*, which are not axioms; since task
#67's campaign closed and task #74 landed, four of the five are gone — `hk`
(`Core.knot_spec`), `hind`/`hinde` (`IndC.ind_routes_spec'` /
`ind_routes_spec_err'`) and `hvar` (`PinsWF.decode_embedded_wf`) discharged
here, `hpins` retired outright by the parametric fold (task #74) — and what
the two `_embedded` corollaries carry is the decoded pins `hp`, the parser's
`hds` and the run `h`. -/

/-- info: 'ConRon.Refine.conron.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists

/-- info: 'ConRon.Refine.conron.no_proof_of_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False

-- The upstream theorems this tier composes with, for comparison: con-leche's
-- own census is the three standard axioms and nothing else.

/-- info: 'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.model_exists

/-- info: 'ConLeche.Cached.no_proof_of_False_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.Cached.no_proof_of_False_cached

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

/-! ## The chunk-level capstones: `hds` discharged by the parser (task #85)

The four theorems above carry `hds` — *"every declaration handed to the fold is
what the port's own smart constructors built"*.  Task #84 put the parser into
the verified core and **task #85 proves it**, so the pair below is the
statement about con-leche's whole pipeline — `builtinPreludeE`, `parseChunks`,
`preparePrelude`, `checkDecls`, the four pure steps of its own main corollary —
with no well-formedness hypothesis about the input at all.

The argument is the one DESIGN.md §3.5 fixed at task #5 and `Refine/PinsWF.lean`
used for the pins: the `*WF` predicates are inductives whose constructors
**are** `name::mk_str`, `level::succ`, `expr::app`, …, and the parse reaches
every node it stores through exactly one of them.  `Refine/Frontend/` threads
one invariant, `Frontend.StateDWF`, through the parse state.

**What stands in `hds`' place is one line about the modeller** (`hgen :
Frontend.ModellerWF inst g`): every declaration `in_model_rec::Modeller
::generate` returns is well formed.  Task #84's seam makes the parse quantify
over that one-method trait, so the 6 428 lines of `crates/con-ron/src/in_model/`
are neither ported nor proved, and what the tower asks of them is that one line
— the maintainer's ruling of 2026-09-13 (*"leave the modeller unverified if you
can; rumors are that upstream can actually get rid of it"*).  It is a promise
about a *function argument*, like `hvar` was before task #66, and it disappears
the day upstream drops the modeller.

**The prelude is a parameter, not a constant.**  con-leche's `builtinPreludeE`
parses an `include_str`; the port's parses a generated byte-array constant of
the crate (task #84's F17).  Identifying the two in the kernel is out of reach
(`AENEAS_FINDINGS.md` §3.8: a string constant of that size expands
quadratically — 27 s at 1 KB, over 300 s at 8 KB), so the headline pair is
**parametric in the prelude's bytes**: it takes them as a variable and `hpre` as
the run of the port's own parser on them, exactly as tasks #74/#75 made the
headline parametric in the pins.  The corollary at the embedded constant is
stated below and costs **nothing extra** — unlike `PINS_TEXT`, the prelude
constant is a `[u8; …]` and not a `&str`, so naming it adds no axiom (task #84
§8).

## The census: the standard three, since task #86

**This pair is pinned at `[propext, Classical.choice, Quot.sound]`, and it took
a Rust change to get there.**  Aeneas renders a `&str` constant as `toStr "…"`
and discharges `toStr`'s bound `s.toByteArray.size ≤ U32.max` with its own
default argument `by decide +native` (`Aeneas/Std/String.lean`, whose own
comment says it should not) — so **every extracted `&str` constant carries a
`_native.decide.ax_1` in its own definition**, before any proof of ours
(`AENEAS_FINDINGS.md` §3.8).  `frontend::scan_fast::key_at` recognised the
dialect's object keys against a table of 66 such constants and `scan_bool`
against two more, so at task #85 every statement that named `parse_chunks` —
which reaches `scan_line_fwd`, which reaches `key_at` — inherited **68** of them
through the closure, with nothing evaluated.

Task #86 spelled all 68 as `[u8; N]` byte arrays, which is what task #84 had
already been forced to do to seven constants of the same module (F17: Aeneas
emits a `&str` constant's double quotes unescaped).  A byte array carries no
axiom, the longest key is eleven bytes so nothing approaches the `Array.make`
limits F17 measured, and the models differ only in that
`core.str.Str.as_bytes S_X` became `lift (Array.to_slice S_X)`.  Not one lemma
of `Refine/Frontend/` moved for it: no proof in that tier ever stepped through
a key comparison, and both spellings reach `match_lit` as a `Slice U8`.

**One `toStr` axiom is left in the whole port**, and it is the one §3.8's
standing ask is about: `kernel::pins_text::PINS_TEXT`, 532 KB of pin text,
which the byte-array route cannot hold — one `Array.make` of that length does
not elaborate, and task #84 measured 512 elements exhausting `maxRecDepth`.
The two `conron.*_embedded` corollaries above are the only theorems that pay
it, and `conron.model_exists_decoded` — which names no constant — is
unaffected either way.
-/

/-- **The main theorem for the whole pipeline** (task #85): every environment
the port accepts, when the declarations it folds are what the port's own parser
produced, has a model in every set theory.  `conron.model_exists_decoded` with
`hds` discharged by `Frontend.parse_chunks_wf` and `Frontend.prepare_prelude_wf`.

It carries `hgen` (the modeller's one promise), `hp` (a decode run), `hpre` (the
prelude's parse, on bytes it does not name), `hparse` (the stream's parse),
`hprep` (the prepare step) and `h` (the check run) — and **no** hypothesis about
well-formedness. -/
theorem conron.model_exists_parsed (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : Frontend.ModellerWF inst g)
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {prelude_bytes : Slice Std.U8} {pre : frontend.export_c.ParseResultD}
    (hpre : frontend.export_c.parse_bytes inst g prelude_bytes true false = ok (.Ok pre))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {in_model census : Bool}
    {r : frontend.export_c.ParseResultD}
    (hparse : frontend.export_c.parse_chunks inst g chunks in_model census = ok (.Ok r))
    {ds : alloc.vec.Vec env.Declaration}
    (hprep : frontend.prepare.prepare_prelude ⟨pre.decls⟩ r.decls = ok ds)
    {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists_decoded V hp
    (Frontend.prepare_prelude_wf (pre := ⟨pre.decls⟩) (Frontend.parse_bytes_wf hgen hpre)
      (Frontend.parse_chunks_wf hgen hparse) hprep) h

/-- **The main corollary for the whole pipeline** (task #85): a stream the port
parses, prepares and accepts never yields a constant of type `False`.
`conron.no_proof_of_False_decoded` with `hds` discharged by the parser. -/
theorem conron.no_proof_of_False_parsed (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : Frontend.ModellerWF inst g)
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {prelude_bytes : Slice Std.U8} {pre : frontend.export_c.ParseResultD}
    (hpre : frontend.export_c.parse_bytes inst g prelude_bytes true false = ok (.Ok pre))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {in_model census : Bool}
    {r : frontend.export_c.ParseResultD}
    (hparse : frontend.export_c.parse_chunks inst g chunks in_model census = ok (.Ok r))
    {ds : alloc.vec.Vec env.Declaration}
    (hprep : frontend.prepare.prepare_prelude ⟨pre.decls⟩ r.decls = ok ds)
    {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False_decoded V hp
    (Frontend.prepare_prelude_wf (pre := ⟨pre.decls⟩) (Frontend.parse_bytes_wf hgen hpre)
      (Frontend.parse_chunks_wf hgen hparse) hprep) h

/-- info: 'ConRon.Refine.conron.model_exists_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists_parsed

/-- info: 'ConRon.Refine.conron.no_proof_of_False_parsed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False_parsed

/-! ### The instance at the prelude the binary ships

`conron.*_parsed` names no constant.  The binary's own prelude is
`frontend::prelude::builtin_prelude_e`, which is `parse_bytes` of
`prelude_text::prelude_text()` — the generated `[u8; 16 922]` in 67 chunks —
and `Frontend.builtin_prelude_e_wf` reads well-formedness off that run without
evaluating a byte of it, exactly as `PinsWF.decode_wf` does for the pins.  So
the pair below costs **nothing beyond what `conron.*_parsed` already costs**:
the prelude constant is a `[u8; 16 922]` in 67 chunks and not a `&str`, so it
adds no `toStr` axiom of its own.  Their censuses, pinned below since task #86,
are therefore the same three, and `Refine/Frontend/Chunks.lean` pins
`builtin_prelude_e_wf`'s, which is what would catch a change. -/

/-- `conron.model_exists_parsed` at the prelude the binary ships. -/
theorem conron.model_exists_prelude (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : Frontend.ModellerWF inst g)
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {pre : frontend.prepare.PreludeIx}
    (hpre : frontend.prelude.builtin_prelude_e inst g = ok (.Ok pre))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {in_model census : Bool}
    {r : frontend.export_c.ParseResultD}
    (hparse : frontend.export_c.parse_chunks inst g chunks in_model census = ok (.Ok r))
    {ds : alloc.vec.Vec env.Declaration}
    (hprep : frontend.prepare.prepare_prelude pre r.decls = ok ds)
    {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    Nonempty (ConLeche.Model V (absEnv e)) :=
  conron.model_exists_decoded V hp
    (Frontend.prepare_prelude_wf (Frontend.builtin_prelude_e_wf hgen hpre)
      (Frontend.parse_chunks_wf hgen hparse) hprep) h

/-- `conron.no_proof_of_False_parsed` at the prelude the binary ships. -/
theorem conron.no_proof_of_False_prelude (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : Frontend.ModellerWF inst g)
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {pre : frontend.prepare.PreludeIx}
    (hpre : frontend.prelude.builtin_prelude_e inst g = ok (.Ok pre))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {in_model census : Bool}
    {r : frontend.export_c.ParseResultD}
    (hparse : frontend.export_c.parse_chunks inst g chunks in_model census = ok (.Ok r))
    {ds : alloc.vec.Vec env.Declaration}
    (hprep : frontend.prepare.prepare_prelude pre r.decls = ok ds)
    {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    ¬ ∃ c ∈ (absEnv e).consts,
        c.toConstantVal.type = .const ConLeche.falseName [] :=
  conron.no_proof_of_False_decoded V hp
    (Frontend.prepare_prelude_wf (Frontend.builtin_prelude_e_wf hgen hpre)
      (Frontend.parse_chunks_wf hgen hparse) hprep) h


/-- info: 'ConRon.Refine.conron.model_exists_prelude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.model_exists_prelude

/-- info: 'ConRon.Refine.conron.no_proof_of_False_prelude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_proof_of_False_prelude

/-! ## The headline of task #87: the file that declares `False` is rejected

con-leche's own main corollary (`ConLeche.no_False_declaration`,
`vendor/con-leche/ConLeche/MainTheorem.lean:110-123`) transported across the
port.  `ConLeche.jsonWithTheoremFalse` (`ConLeche/Accepts.lean:62-73`) is the
*file*-level shape: four JSON lines, in order, anywhere in the byte stream —
a name entry `False`, an expression entry that is that constant, a name entry
for the theorem, and a `thm` record of that name, that type and any proof.  The
statement below says that **the port** — its scanner, its line applier, its two
permuting passes and its fold — never accepts such a stream.

Four steps, con-leche's, one port lemma each:

1. `Frontend.parse_chunks_refines_of_specs` (`Refine/Frontend/ChunksR.lean`),
   which is `parse_chunks_refines` at `Frontend.parseIngredients`, says the
   port's parse *is* `parseChunks` of the abstracted chunks, so
   `ConLeche.Frontend.parseChunks_jsonWithTheoremFalse`
   (`Verify/Frontend/FileFalse.lean:177`) applies and hands back a theorem
   record of type `False` among con-leche's parsed declarations;
   `ParseResultSim.decls` moves it back onto the port's own records.
2. `Frontend.prepare_prelude_refines` (`Refine/Frontend/PrepareR.lean:1889`)
   says the prepared stream is `preparePrelude` of those records, and
   `ConLeche.Frontend.mem_preparePrelude` (`Verify/Frontend/Prepare.lean:174`)
   says preparation keeps every one of them.
3. `check_decls_verified_refines_ok` turns the port's accept into con-leche's.
4. `ConLeche.no_False_theorem_accepted` (`Verify/Cached/StreamThm.lean:207`)
   refutes that accept.

**The prelude never has to be identified with con-leche's.**  Step 2's
`mem_preparePrelude` holds for *every* `pre`, so the statement is
prelude-parametric for free — the same move tasks #74/#75 made for the pins,
and the reason task #84's F17 (a `&str` constant of that size does not
elaborate, `AENEAS_FINDINGS.md` §3.8) costs this theorem nothing.

### What remains trusted

* `hgen : Frontend.ModellerWF inst g` — phase 1's promise about the unverified
  modeller (task #84's seam): every declaration `in_model_rec::Modeller
  ::generate` returns is well formed.  It is what discharges the fold's `hds`.
* `hu : Frontend.Utf8DecodeSpec`, `hun : Frontend.UnescapeSpec`,
  `hsp : Frontend.IndRSpec inst g` and `hspec : Frontend.HoistSpec` — phase 3's
  outstanding ingredients, stated as hypotheses rather than assumed as axioms
  (the `Refine/IndSpec.lean` idiom).  The first three are the *whole* residue in
  front of the port's streaming parse: `Frontend.parseIngredients`
  (`Refine/Frontend/ChunksR.lean`) builds the nine-field `ParseIngredients`
  record out of them, so the parse hypothesis is three named `Prop`s with
  owners — the string tier owes the first two, the inductive tier the third —
  and not a record somebody must assemble.  `hspec` is the hoist's target pass
  (`PrepareR.lean:1629`).  Discharging the four is what is left of task #87.
* The driver: that `con_ron::driver` calls `parse_chunks`, `prepare_prelude`
  and `check_decls` on the stream it was handed, in this order — the same
  unverified line `conron.model_exists_decoded` already owes for the pins.

Nothing else: the census below is Lean's own three axioms.
-/

/-- **A file that declares a theorem of type `False` is rejected by the port**
(task #87) — `ConLeche.no_False_declaration` transported.  Parametric in the
prelude, as `conron.model_exists_parsed` is: `hpre` is the port's own parse of
*some* prelude bytes, never identified with con-leche's `builtinPreludeE`.

It carries `hgen` (the modeller's promise, phase 1), `hu`/`hun`/`hsp`/`hspec`
(phase 3's outstanding ingredients — the parse's three named `Prop`s, through
`Frontend.parseIngredients`, and the hoist's), `hp` (a decode run), `hpre` (the
prelude's parse), `hparse` (the stream's parse), `hprep` (the prepare step) and
`h` (the check run) — and no hypothesis about well-formedness at all. -/
theorem conron.no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : Frontend.ModellerWF inst g)
    (hu : Frontend.Utf8DecodeSpec) (hun : Frontend.UnescapeSpec)
    (hsp : Frontend.IndRSpec inst g) (hspec : Frontend.HoistSpec)
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {prelude_bytes : Slice Std.U8} {pre : frontend.export_c.ParseResultD}
    (hpre : frontend.export_c.parse_bytes inst g prelude_bytes true false = ok (.Ok pre))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {im ce : Bool}
    (hfalse : ConLeche.jsonWithTheoremFalse (Frontend.absChunks chunks))
    {r : frontend.export_c.ParseResultD}
    (hparse : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Ok r))
    {ds : alloc.vec.Vec env.Declaration}
    (hprep : frontend.prepare.prepare_prelude ⟨pre.decls⟩ r.decls = ok ds)
    {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    False := by
  -- 1. the parse: the port's records hold the theorem record of type `False`
  obtain ⟨x, hx, hsim⟩ := Frontend.parse_chunks_refines_of_specs hu hun hsp hparse
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hx
  have hmem : ConLeche.Declaration.thmDecl cv vl ∈ Frontend.absDecls r.decls := by
    rw [Frontend.absDecls, hsim.decls]; exact Array.mem_toList_iff.mpr hmem
  -- 2. the preparation keeps it
  have hprel : Frontend.PreludeIxWF ⟨pre.decls⟩ := Frontend.parse_bytes_wf hgen hpre
  have hrwf : ∀ d ∈ r.decls.val, DeclarationWF d := Frontend.parse_chunks_wf hgen hparse
  have hmem' : ConLeche.Declaration.thmDecl cv vl
      ∈ (⟨ds.val.map absDeclaration⟩ : Array ConLeche.Declaration) := by
    have hpp := Frontend.prepare_prelude_refines hspec hprel hrwf hprep
    refine Array.mem_toList_iff.mp ?_
    show ConLeche.Declaration.thmDecl cv vl ∈ Frontend.absDecls ds
    rw [hpp]
    exact Array.mem_toList_iff.mpr
      (ConLeche.Frontend.mem_preparePrelude (pre := Frontend.absPreludeIx ⟨pre.decls⟩)
        (Array.mem_toList_iff.mp (by simpa using hmem)))
  -- 3./4. the fold's accept is con-leche's, and con-leche refutes it
  exact ConLeche.no_False_theorem_accepted V _ cv vl hmem' hty (absEnv e)
    (check_decls_verified_refines_ok (Core.knot_spec IndAbs.checkFuelU)
      conron.basis_raw_spec
      (InductivesC.ind_routes_spec' (Core.knot_spec IndAbs.checkFuelU))
      (InductivesC.ind_routes_spec_err' (Core.knot_spec IndAbs.checkFuelU))
      (PinsWF.decode_wf hp)
      (Frontend.prepare_prelude_wf hprel hrwf hprep) h)

/-- info: 'ConRon.Refine.conron.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_False_declaration

/-- `conron.no_False_declaration` at the prelude the binary ships,
`frontend::prelude::builtin_prelude_e` — the pairing
`conron.model_exists_parsed` / `conron.model_exists_prelude` uses, and free for
the same reason: the prelude constant is a `[u8; 16 922]` and not a `&str`, so
naming it adds no `toStr` axiom (task #84 §8, task #86). -/
theorem conron.no_False_declaration_prelude (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : Frontend.ModellerWF inst g)
    (hu : Frontend.Utf8DecodeSpec) (hun : Frontend.UnescapeSpec)
    (hsp : Frontend.IndRSpec inst g) (hspec : Frontend.HoistSpec)
    {text : Slice Std.U8} {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode text = ok (.Ok pins))
    {pre : frontend.prepare.PreludeIx}
    (hpre : frontend.prelude.builtin_prelude_e inst g = ok (.Ok pre))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {im ce : Bool}
    (hfalse : ConLeche.jsonWithTheoremFalse (Frontend.absChunks chunks))
    {r : frontend.export_c.ParseResultD}
    (hparse : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Ok r))
    {ds : alloc.vec.Vec env.Declaration}
    (hprep : frontend.prepare.prepare_prelude pre r.decls = ok ds)
    {e : env.Env}
    (h : cached.installed.check_decls .Verified pins ds = ok (.Ok e)) :
    False := by
  obtain ⟨x, hx, hsim⟩ := Frontend.parse_chunks_refines_of_specs hu hun hsp hparse
  obtain ⟨cv, vl, hty, hmem⟩ := ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hx
  have hmem : ConLeche.Declaration.thmDecl cv vl ∈ Frontend.absDecls r.decls := by
    rw [Frontend.absDecls, hsim.decls]; exact Array.mem_toList_iff.mpr hmem
  have hprel : Frontend.PreludeIxWF pre := Frontend.builtin_prelude_e_wf hgen hpre
  have hrwf : ∀ d ∈ r.decls.val, DeclarationWF d := Frontend.parse_chunks_wf hgen hparse
  have hmem' : ConLeche.Declaration.thmDecl cv vl
      ∈ (⟨ds.val.map absDeclaration⟩ : Array ConLeche.Declaration) := by
    have hpp := Frontend.prepare_prelude_refines hspec hprel hrwf hprep
    refine Array.mem_toList_iff.mp ?_
    show ConLeche.Declaration.thmDecl cv vl ∈ Frontend.absDecls ds
    rw [hpp]
    exact Array.mem_toList_iff.mpr
      (ConLeche.Frontend.mem_preparePrelude (pre := Frontend.absPreludeIx pre)
        (Array.mem_toList_iff.mp (by simpa using hmem)))
  exact ConLeche.no_False_theorem_accepted V _ cv vl hmem' hty (absEnv e)
    (check_decls_verified_refines_ok (Core.knot_spec IndAbs.checkFuelU)
      conron.basis_raw_spec
      (InductivesC.ind_routes_spec' (Core.knot_spec IndAbs.checkFuelU))
      (InductivesC.ind_routes_spec_err' (Core.knot_spec IndAbs.checkFuelU))
      (PinsWF.decode_wf hp)
      (Frontend.prepare_prelude_wf hprel hrwf hprep) h)

/-- info: 'ConRon.Refine.conron.no_False_declaration_prelude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms conron.no_False_declaration_prelude

end ConRon.Refine
