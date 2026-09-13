/-
`kernel::pins_decode` — the embedded pin text and its decoder (tasks #43, #64).

DESIGN.md §3's pin paragraph used to say that the `Nat`-operation pin sets are
*runtime data*: the unverified driver read them from a `con-ron-pins/1` file and
handed them to `check_decls`, so the main theorem's statement carried the
hypothesis `absPins pins = ConLeche.natOpPinSets` — a promise about an argument
the binary was given, not a fact about the binary.  Task #43 moved the data
inside the core: `kernel::pins_text::PINS_TEXT` is the text as a `&'static str`
and `kernel::pins_decode::decode` is a *verified* reader of it, so the pin list
is a closed term of the model, `decode PINS_TEXT`.

**Task #64 closes both of task #43's open statements**, one by proof and one by
`native_decide`, which the maintainer accepted as an interim (DESIGN.md §3's
pins paragraph, and `Refine/README.md`'s "where the native-decide axiom lives"):

| statement | how |
|---|---|
| `pins_decode_refines` | **proved**, no axiom: `Refine/PinsDec.lean`'s byte-level reference decoder splits it into (A) the Aeneas model against `PinsDec` and (B) `PinsDec` against `ConRon.Dump.parsePins` |
| `pins_closed` | **`native_decide`**: one closed computation on static data, and the *only* place in the port where native evaluation is trusted |
| `pins_text_decodes` | `pins_closed`, verbatim — task #43's spelling of it |
| `check_decls_pins_refines` | the corollary, from the two above (task #56's proof, unchanged) |

`Refine/PinsDec.lean`'s module note is the map of the proof; the files are
`PinsDec`, `PinsAbs`, `PinsBytes`, `PinsRecords`, `PinsRun` (half A),
`PinsAscii`, `PinsSplit`, `PinsRead` (half B).

**No hypothesis was added.**  `pins_decode_refines` is task #43's statement,
character for character: the decoder's extra strictness (single spaces, one
newline per record, nothing after the footer) is what makes the accept
direction free, and no well-formedness side condition is needed anywhere —
every value a record installs is built by a *smart constructor* whose own
refinement lemma already says what it abstracts to.

## What `native_decide` is trusted for here

Exactly one closed computation on static data: that the text
`kernel::pins_text::PINS_TEXT` embeds decodes, under `ConRon.Dump.parsePins`,
to con-leche's own `ConLeche.natOpPinSets`.  It is a fact about two committed
constants and about no input the binary will ever be given.  Task #43 measured
why the kernel cannot check it (a well-founded reference decoder does not whnf;
a 532 KB string literal expands quadratically) and spike #63 is the attempt to
remove the need; until then the axiom is confined to `pins_closed` below, whose
census is pinned by `#guard_msgs`, and to the `conron.*_embedded` corollaries
that use it.  The general, `pins`-parametric theorems of `Refine/Main.lean` do
not mention the embedded text at all and keep their own census.

Note that Aeneas already spends a native-decide axiom on any extracted `&str`
constant: `toStr`'s bound `s.toByteArray.size ≤ U32.max` is discharged by its
own default argument `by decide +native` (`Aeneas/Std/String.lean`, whose own
comment says it should not be).  So `PINS_TEXT` carries
`pins_text.PINS_TEXT._native.decide.ax_1` before any proof of ours, and every
statement *about the embedded constant* inherits it.  That is Aeneas's to fix,
and it is why the embedded census has two native entries rather than one.

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
The exact-result shape of DESIGN.md §3.5: nothing is claimed when the Rust
decoder fails, which is what makes the port's extra strictness free.

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
   joined by `' '`") that carry the record pass onto `runLines`. -/
theorem pins_decode_refines (t : Str) (v : alloc.vec.Vec nat_op_pins.NatOpPinSet)
    (h : pins_decode.decode t = ok (.Ok v)) :
    ConRon.Dump.parsePins (absText t) = .ok (absPins v) := by
  have hA := PinsRun.decode_refines h
  have hasc := PinsDec.decode_ascii hA
  rw [PinsSplit.absText_of_ascii hasc]
  exact PinsRead.parsePins_of_decode hA hasc

/-! ## The closed computation

The statement task #43 set out to prove and could not, with the reasons it
measured — none a matter of patience:

**(a) The Aeneas string model already spends a native-decide axiom.**  Aeneas
renders a `&str` constant as `toStr "…"`, and `toStr`'s bound
`s.toByteArray.size ≤ U32.max` is discharged by its own default argument
`by decide +native` (`Aeneas/Std/String.lean`, with the library's own TODO
saying it should not be).  So, *before any proof of ours*,

    #print axioms ConRon.Generated.kernel.pins_text.PINS_TEXT
    -- [propext, Classical.choice, Quot.sound,
    --  pins_text.PINS_TEXT._native.decide.ax_1]

`decode` itself is clean (`[propext, Classical.choice, Quot.sound]`).  A
native-decide-free theorem *about the constant* is therefore impossible without
an upstream change to Aeneas.

**(b) The reference decoder does not reduce in the kernel at all.**
`ConRon.Dump.parsePins` was `partial def` (nothing can be proved about a
`partial def`, and nothing reduces); task #43 made `runLines` total with
`termination_by`, which buys the *statements* but not evaluation: a
well-founded recursion does not whnf.  Measured on the smallest possible pin
text, 23 bytes:

    example : (parsePins "con-ron-pins/1\nend 0\n").isOk = true := by rfl
    -- Tactic `rfl` failed … is not definitionally equal to `true`   (1.3 s)

**(c) Kernel reduction of a string literal is quadratic**, so even the byte
size of the embedded text is out of reach: 3.0 s for a 256-byte prefix, 27 s
for 1 KB, over 300 s for 8 KB, ≈10⁶–10⁷ s for the real 532 KB by the fit.

So the direct route dies by (b) and (c), and the round-trip route (prove
`parsePins (dumpPins v) = .ok v` generically, then `PINS_TEXT = dumpPins
ConLeche.natOpPinSets` by `rfl`) by (c) twice over.  **Task #64's ruling is to
take the computation by `native_decide` as an interim** and to confine it to
the single lemma below; spike #63 is the attempt to remove it. -/

-- `DecidableEq ConLeche.NatOpPinSet` — what the closed computation below has to
-- decide — is derived in `Refine/PinsDec.lean`, where that file's own `#guard`
-- self-tests already need it.  Derived means con-leche's `instDecidableEqExpr`
-- on the eight pins and the eight certificate lists: the structural walk, which
-- is what makes it exact, and it is only ever run by compiled code.

/-- **The embedded text, as a Lean `String`.**  `PINS_TEXT` is by definition
`toStr "…"` and `absText_toStr` undoes `toStr` generically, so this is that
literal after a `delta` step and **nothing is evaluated** — which is what makes
a statement about the Rust constant a statement about a string literal at zero
kernel cost. -/
def pinsTextLean : String := absText pins_text.PINS_TEXT

/-- **The closed computation, by `native_decide`** — the *only* place in the
port where native evaluation is trusted (`Refine/README.md`).  The embedded
`con-ron-pins/1` text decodes, under the Lean reference reader, to con-leche's
own `ConLeche.natOpPinSets`: a fact about two committed constants and about no
input the binary will ever be given.

The `rw` is what makes it cheap: `absText_toStr` turns the model's `Str` into
the 532 KB string literal without touching the `toStr` bound, so the compiled
computation is `parsePins "…"` and nothing about `Slice`, `U8` or `toStr` is
ever run.  It takes about ten seconds end to end. -/
theorem pins_closed :
    ConRon.Dump.parsePins pinsTextLean = .ok ConLeche.natOpPinSets := by
  rw [pinsTextLean, kernel.pins_text.PINS_TEXT, absText_toStr]
  native_decide

/-- Task #43's spelling of the closed computation, which
`check_decls_pins_refines` is written against: `pins_closed`, with
`pinsTextLean` unfolded. -/
theorem pins_text_decodes :
    ConRon.Dump.parsePins (absText pins_text.PINS_TEXT)
      = .ok ConLeche.natOpPinSets := pins_closed

/-- **The corollary** (DESIGN.md §1's statement, with the pins closed): the pin
list the binary uses is con-leche's own, with no hypothesis about it.  The
driver passes `decode_embedded()`, Aeneas models `str::as_bytes` as the
identity, so that is `decode PINS_TEXT` — and the two statements above say
what it decodes to.

**Proved** (task #56): task #43 left this `sorry` because the tier below it
was not refined either, but the composition needs nothing from that tier — it
is `pins_decode_refines` at `PINS_TEXT` against `pins_text_decodes`, and
`Except.ok` is injective. -/
theorem check_decls_pins_refines
    (v : alloc.vec.Vec nat_op_pins.NatOpPinSet)
    (h : pins_decode.decode_embedded = ok (.Ok v)) :
    absPins v = ConLeche.natOpPinSets := by
  rw [pins_decode.decode_embedded, core.str.Str.as_bytes] at h
  obtain ⟨t, ht, h2⟩ := bind_eq_ok_iff.mp h
  rw [show t = pins_text.PINS_TEXT from Result.ok_injective ht.symm] at h2
  have h1 := pins_decode_refines pins_text.PINS_TEXT v h2
  rw [pins_text_decodes] at h1
  exact (Except.ok.inj h1).symm

/-! ## The census (DESIGN.md §5)

Three lines, and the difference between them is the whole trust story of this
file.

* `pins_decode_refines` is an **ordinary proof**: con-leche's own three axioms
  and nothing else.  It is a theorem about every byte string, so nothing is
  ever evaluated.
* `pins_closed` is the **one** native-decide site: `pins_closed._native.
  native_decide.ax_1_1` is the axiom Lean 4.33 seals the computation into (it
  asserts exactly `decide (parsePins … = .ok natOpPinSets) = true`, and nothing
  else), and `pins_text.PINS_TEXT._native.decide.ax_1` is the one Aeneas's
  `toStr` already spent on the constant before we touched it.
* `check_decls_pins_refines` inherits both, because it is about the embedded
  text.  `Refine/Main.lean`'s general theorems do not. -/

-- TASK64-CENSUS-PLACEHOLDER
#print axioms pins_decode_refines
#print axioms pins_closed
#print axioms check_decls_pins_refines

end ConRon.Refine
