/-
`kernel::pins_decode` — the embedded pin text and its decoder (tasks #43, #64,
#74).

DESIGN.md §3's pin paragraph used to say that the `Nat`-operation pin sets are
*runtime data*: the unverified driver read them from a `con-ron-pins/1` file and
handed them to `check_decls`, so the main theorem's statement carried the
hypothesis `absPins pins = ConLeche.natOpPinSets` — a promise about an argument
the binary was given, not a fact about the binary.  Task #43 moved the data
inside the core: `kernel::pins_text::PINS_TEXT` is the text as a `&'static str`
and `kernel::pins_decode::decode` is a *verified* reader of it, so the pin list
is a closed term of the model, `decode PINS_TEXT`.

**Task #64 closed both of task #43's open statements**, one by proof and one by
`native_decide` (accepted as an interim), and **task #74 retired the second
one**: con-leche's own fold takes the pin list as an argument now (its task
#285, vendored here), so there is no `absPins pins = natOpPinSets` left to
discharge and nothing in the port is evaluated natively.  What this file states
is the one statement that was always an ordinary proof:

| statement | how |
|---|---|
| `pins_decode_refines` | **proved**, no axiom: `Refine/PinsDec.lean`'s byte-level reference decoder splits it into (A) the Aeneas model against `PinsDec` and (B) `PinsDec` against `ConRon.Dump.parsePins` |

`Refine/PinsDec.lean`'s module note is the map of the proof; the files are
`PinsDec`, `PinsAbs`, `PinsBytes`, `PinsRecords`, `PinsRun` (half A),
`PinsAscii`, `PinsSplit`, `PinsRead` (half B).  What the *decoded* list is good
for beyond its own refinement is `Refine/PinsWF.lean`'s `decode_embedded_wf`:
`PinsWF` for the embedded run, which is the one thing `Refine/Main.lean`'s
`conron.*_embedded` corollaries still ask of the pins.

**No hypothesis was added.**  `pins_decode_refines` is task #43's statement,
character for character: the decoder's extra strictness (single spaces, one
newline per record, nothing after the footer) is what makes the accept
direction free, and no well-formedness side condition is needed anywhere —
every value a record installs is built by a *smart constructor* whose own
refinement lemma already says what it abstracts to.

## Nothing is trusted to native evaluation here any more

Task #64's `pins_closed` was the port's single `native_decide` site, and
`Refine/README.md`'s "where the native-decide axiom lives" was the standing
statement of what it bought.  It is gone (task #74, the section below says
exactly what went with it).  Note that Aeneas still spends a native-decide
axiom on any extracted `&str` constant — `toStr`'s bound
`s.toByteArray.size ≤ U32.max` is discharged by its own default argument
`by decide +native` (`Aeneas/Std/String.lean`, whose own comment says it should
not be) — so `kernel::pins_text::PINS_TEXT` carries
`pins_text.PINS_TEXT._native.decide.ax_1` before any proof of ours, and any
statement whose closure *evaluates* the constant would inherit it.  None does:
`pins_decode_refines` is generic in the byte string, and `decode_embedded_wf`
holds for every byte string too.

## `sorry` count in this file: 0
-/
import ConRon.Refine.PinsAbs
import ConRon.Refine.PinsRun
import ConRon.Refine.PinsRead
import ConRon.Dump.Read

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-! ## The refinement of the decoder -/

/-- **The decoder refines the reference reader.**  If the Rust decoder accepts
the byte slice `t` and returns `v`, then `ConRon.Dump.parsePins` — the Lean
reader of `con-ron-pins/1` that task #31 validated against con-leche's own
`natOpPinSets` — accepts `absText t` and returns the same list of variants.
Nothing is claimed when the Rust decoder fails, which is what makes the port's
extra strictness free.

**Proved** (task #64), through the byte-level reference decoder
`ConRon.Refine.PinsDec`, which is `kernel::pins_decode` function for function
over a `List Nat` suffix.  Task #43's five pieces survive as the five files
below it, in the same dependency order:

1. `Refine/PinsBytes.lean` — the scalars, the escape and the references, each
   as "the model's reader at `(t, i)` is `PinsDec`'s at `bytesFrom t i`";
2. `Refine/PinsRecords.lean` — the `N`/`L`/`W`/`E` records, one
   smart-constructor lemma each;
3. `Refine/PinsRun.lean` — the `S` record and the pass, where the byte index
   becomes `PinsDec.runRecords`' fuel;
4. `Refine/PinsAscii.lean` — every byte the decoder accepts is ASCII, which is
   what makes `absText` (a UTF-8 *decode*) readable character for character;
5. `Refine/PinsSplit.lean` + `Refine/PinsRead.lean` — the tokenizer bridge:
   `String.splitOn` at a one-character separator, and the two invariants
   ("the bytes left are the lines left, joined by `'\n'`"; "…the fields left,
   joined by `' '`") that carry the record pass onto `runLines`.

**Over the whole outcome** (task #67, DESIGN.md §3's ruling of 2026-09-13):
the `.Err` branch claims *nothing*, and has to.  `kernel::pins_decode` is the
one module of the port whose errors are wholly its own — con-leche has no byte
decoder to mirror, its `natOpPinSets` being elaboration-time data
(`ConLeche/Kernel/NatOpPins.lean:61`) — so all twenty-eight of its throws go
through `pins_decode::bad_text`, a `CheckError::Native`, and `absErrKind` sends
every one of them to `none`.  `Refine/PinsBytes.lean`'s `bad_text_native` is
where that is pinned down.

The outcome is an explicit argument because the result binder `v` it replaces
was one; `pins_decode_refines_ok` below is the pre-#67 statement, verbatim. -/
theorem pins_decode_refines (t : Str)
    (o : core.result.Result (alloc.vec.Vec nat_op_pins.NatOpPinSet)
        core_types.CheckError)
    (h : pins_decode.decode t = ok o) :
    match o with
    | .Ok v => ConRon.Dump.parsePins (absText t) = .ok (absPins v)
    | .Err ce => absErrKind ce = none := by
  cases o with
  | Err ce => exact PinsRun.decode_refines h
  | Ok v =>
    have hA : PinsDec.decode (bytesOf t) = some (absPins v) := PinsRun.decode_refines h
    have hasc := PinsDec.decode_ascii hA
    rw [PinsSplit.absText_of_ascii hasc]
    exact PinsRead.parsePins_of_decode hA hasc

/-- `pins_decode_refines` at a success, the pre-#67 statement. -/
theorem pins_decode_refines_ok (t : Str)
    (v : alloc.vec.Vec nat_op_pins.NatOpPinSet)
    (h : pins_decode.decode t = ok (.Ok v)) :
    ConRon.Dump.parsePins (absText t) = .ok (absPins v) :=
  pins_decode_refines t (.Ok v) h

/-! ## The closed computation is gone (task #74)

Task #64 proved one more statement here, `pins_closed`, by `native_decide`:
that the embedded text decodes to con-leche's own `ConLeche.natOpPinSets`.  It
was needed because the cited `checkDivModPin` read that global, so the tower's
statements carried `hpins : absPins pins = ConLeche.natOpPinSets` and somebody
had to discharge it for the list the binary threads.  Three obstacles made the
kernel unable to check it — Aeneas's `toStr` already spends a native-decide
axiom on every extracted `&str`; a well-founded reference decoder does not
whnf; kernel reduction of a string literal is quadratic, so even the byte size
of a 532 KB literal is out of reach — and DESIGN.md §3 recorded the interim.

**Task #74 removes the need instead of the obstacles.**  con-leche's task #285
makes the pin list an argument of the fold, so `check_decls_refines` is
*already* the statement at whatever list the binary threads and there is
nothing to identify with a constant.  `pins_closed`, `pins_text_decodes`,
`pinsTextLean` and `check_decls_pins_refines` are therefore deleted, with
`Refine/Installed.lean`'s `check_decls_embedded_refines` and
`Refine/Main.lean`'s two uses of it, and `Refine/BasisPins.lean`'s
`nat_op_pin_sets_refines`, which was the same corollary stated twice.  No
`native_decide` is invoked anywhere in `proof/` any more, and the port's own
sealed axiom is gone from the `conron.*_embedded` census; what those two still
inherit is Aeneas's `toStr` axiom on the *definition* of the extracted `&str`
constant they name (`AENEAS_FINDINGS.md` §3.8), which no proof of ours can
drop.

What survives about the embedded text is what does not need evaluating:
`pins_decode_refines` above (an ordinary proof, about *every* byte string) and
`Refine/PinsWF.lean`'s `decode_embedded_wf`, which is what the `_embedded`
corollaries still use — for `PinsWF`, never for the pins' value. -/

/-! ## The census (DESIGN.md §5)

One line, and it is an **ordinary proof**: `pins_decode_refines` depends on
con-leche's own three axioms and nothing else.  It is a theorem about every
byte string, so nothing is ever evaluated — which is why the file that used to
be the port's one native-evaluation site now has none at all (task #74). -/

/-- info: 'ConRon.Refine.pins_decode_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pins_decode_refines

end ConRon.Refine
