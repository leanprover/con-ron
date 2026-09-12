/-
`kernel::pins_decode` — the embedded pin text and its decoder (task #43).

DESIGN.md §3's pin paragraph used to say that the `Nat`-operation pin sets are
*runtime data*: the unverified driver read them from a `con-ron-pins/1` file and
handed them to `check_decls`, so the main theorem's statement carried the
hypothesis `absPins pins = ConLeche.natOpPinSets` — a promise about an argument
the binary was given, not a fact about the binary.  Task #43 moves the data
inside the core: `kernel::pins_text::PINS_TEXT` is the text as a `&'static str`
and `kernel::pins_decode::decode` is a *verified* reader of it, so the pin list
is now a closed term of the model, `decode PINS_TEXT`.

This file is where that cashes in, and where it does not.  One lemma proved
(`absText_toStr`, the bridge from the Rust constant to a Lean string literal,
at zero kernel cost) and three statements:

* `pins_decode_refines` — the Rust decoder computes what the Lean reference
  reader (`ConRon.Dump.parsePins`, task #31) computes.  The exact-result shape
  of DESIGN.md §3.5: nothing is claimed when the Rust side fails, and the Rust
  side is deliberately the stricter of the two (`kernel/pins_decode.rs`'s
  module note).  **Open** — its own docstring has the decomposition and what
  each piece costs.
* `pins_text_decodes` — the *closed computation*
  `ConRon.Dump.parsePins <the embedded text> = .ok ConLeche.natOpPinSets`.
  **Open, and task #43 measured why it is out of reach in this Lean**: see the
  docstring, which is the task's main finding.
* `check_decls_pins_refines` — the shape the corollary takes once the two
  above hold: `check_decls`' pin argument is `decode PINS_TEXT` and no
  hypothesis about the pins is left.  Stated, `sorry`, because the tiers below
  it (`cached::installed`) are not refined yet either.

Nothing here is used by the runtime; `cargo test` and `scripts/gen-pins.sh
--check` are what hold the embedded text to con-leche's value today.
-/
import ConRon.Refine.Expr
import ConRon.Dump.Read
import ConLeche.Kernel.NatOpPins

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-! ## The abstractions -/

/-- A `&str` of the model as a Lean `String`.  Aeneas models `Str` as
`Slice U8` (`Aeneas/Std/StringDef.lean`) and a `&str` *constant* as
`toStr "…"`, so this is the left inverse of `toStr` on the constant: the bytes
are UTF-8 by construction, and `String.fromUTF8?` is total on them.  A
malformed byte string abstracts to `""`, which no statement below relies on —
`absText (toStr s) = s` (`absText_toStr`) is what is used, and that is generic
in `s`. -/
def absText (t : Str) : String :=
  match String.fromUTF8? ⟨(t.val.map (fun b => UInt8.ofNat b.val)).toArray⟩ with
  | some s => s
  | none => ""

/-- A pin variant of the model as `ConLeche.NatOpPinSet`
(`ConLeche/Kernel/NatOpPinSet.lean:26-49`): the toolchain string, the eight
pinned defining expressions and the eight certificate lists, field for field,
through the abstractions of `ConRon/Refine/Abs.lean`. -/
def absNatOpPinSet (s : nat_op_pins.NatOpPinSet) : ConLeche.NatOpPinSet :=
  { toolchain := absString s.toolchain
    divPin := absExpr s.div_pin
    modPin := absExpr s.mod_pin
    gcdPin := absExpr s.gcd_pin
    landPin := absExpr s.land_pin
    lorPin := absExpr s.lor_pin
    xorPin := absExpr s.xor_pin
    shiftLeftPin := absExpr s.shift_left_pin
    shiftRightPin := absExpr s.shift_right_pin
    divProofs := absExprs s.div_proofs
    modProofs := absExprs s.mod_proofs
    gcdProofs := absExprs s.gcd_proofs
    landProofs := absExprs s.land_proofs
    lorProofs := absExprs s.lor_proofs
    xorProofs := absExprs s.xor_proofs
    shiftLeftProofs := absExprs s.shift_left_proofs
    shiftRightProofs := absExprs s.shift_right_proofs }

/-- The pin list: a `Vec<NatOpPinSet>` as `List ConLeche.NatOpPinSet`, in file
order — which is the order `checkDivModPinLoop` tries the variants in, so the
order is part of the statement. -/
def absPins (ps : alloc.vec.Vec nat_op_pins.NatOpPinSet) :
    List ConLeche.NatOpPinSet :=
  ps.val.map absNatOpPinSet

/-! ## The bridge to the embedded text

`PINS_TEXT` is `toStr "<the 532 456-byte literal>"` in the generated model, so
`absText PINS_TEXT` is *definitionally* `absText (toStr pinsTextLean)` for the
Lean string literal `pinsTextLean` — a `delta` step and no computation.  What
makes that useful is that `absText (toStr s) = s` holds **generically**: it is
`Slice.from_val` (the `Slice` bound is a *parameter* of `toStr`, so reading the
list back never touches it) followed by `String.fromUTF8?_toByteArray`.  The
alternative — evaluating anything about the literal — is what the measurement
in `pins_text_decodes` rules out. -/

/-- `ByteArray.toList` is its array's list.  Lean 4.33's core defines
`ByteArray.toList` as a reverse-accumulating loop and proves nothing about it
(Aeneas hits the same wall and proves the sibling `length_toList` by hand in
`Aeneas/Std/String.lean`), so the loop invariant is spelled out here: at index
`i` with accumulator `r`, the loop yields `r.reverse ++ drop i`. -/
theorem ByteArray.toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  have h : ∀ i r, ByteArray.toList.loop b i r
      = r.reverse ++ b.data.toList.drop i := by
    intro i r
    fun_induction ByteArray.toList.loop b i r with
    | case1 i r hi ih =>
      rw [ih]; simp
      have hlt : i < b.data.toList.length := by rw [Array.length_toList]; exact hi
      rw [List.drop_eq_getElem_cons hlt]
      have : b.data[i]! = b.data[i]'(by rw [← Array.length_toList]; exact hlt) :=
        getElem!_pos b.data i (by rw [← Array.length_toList]; exact hlt)
      simp [ByteArray.get!, this]
    | case2 i r hi => simp; omega
  rw [ByteArray.toList]
  simpa using h 0 []

/-- The byte a `U8` of the model abstracts to is the byte it was made from:
`toStr`'s `UInt8 → U8` map is undone by `absText`'s `U8 → UInt8` one. -/
@[simp] theorem u8_ofNat_val (a : UInt8) :
    UInt8.ofNat (a.toBitVec#uscalar : U8).val = a := by
  unfold Std.UScalar.val; simp [UInt8.ofNat]

/-- Decoding a string's own UTF-8 gives the string back.  `String` is a
structure over a `ByteArray` with a validity field in 4.33, so this is
`dif_pos` on that field. -/
theorem String.fromUTF8?_toByteArray (s : String) :
    String.fromUTF8? s.toByteArray = some s := by
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

/-- **`absText` undoes `toStr`**, for every string and independently of how the
`toStr` bound was proved — the bound is a *parameter*, and `Slice.from_val`
reads the list back without looking at it.  This is the one lemma that turns a
statement about the Rust constant into a statement about a Lean string literal
at **zero** kernel cost: `PINS_TEXT` is by definition `toStr "…"`, so
`absText PINS_TEXT` is that literal after one `delta` step and nothing is ever
evaluated. -/
theorem absText_toStr (s : String) (h : s.toByteArray.size ≤ U32.max) :
    absText (toStr s h) = s := by
  unfold absText toStr
  simp [Slice.from_val, ByteArray.toList_eq, Function.comp_def]
  -- `{ data := s.toByteArray.data }` *is* `s.toByteArray` (structure eta), which
  -- `show` sees and `rw` cannot: the hidden validity proof depends on it.
  show (match String.fromUTF8? s.toByteArray with | some s => s | none => "") = s
  rw [String.fromUTF8?_toByteArray]

/-! ## The refinement of the decoder -/

/-- **The decoder refines the reference reader.**  If the Rust decoder accepts
the byte slice `t` and returns `v`, then `ConRon.Dump.parsePins` — the Lean
reader of `con-ron-pins/1` that task #31 validated against con-leche's own
`natOpPinSets` — accepts `absText t` and returns the same list of variants.
The exact-result shape of DESIGN.md §3.5: nothing is claimed when the Rust
decoder fails, which is what makes the port's extra strictness free.

**Open.**  What it needs is not hard in kind but long in bulk: the decoder is
50 functions, and the statement relates a byte-index pass to `parsePins`'
line-split-then-token-split pass, so the induction carries a relation between
"the byte at index `i` starts record number `k`" and "the `k`-th line of
`String.splitOn "\n"`".  The pieces, in dependency order:

1. the tokenizer bridge: for a byte range with no `' '`/`'\n'`, the decoder's
   scan and `String.splitOn`'s token agree.  This is where the work is —
   `String.splitOn` in Lean 4.33 is written on `String.Pos` and the lemmas
   relating it to `List Char` are not in core;
2. the scalars: `read_nat`/`read_index`/`read_big_nat` against `natTok`
   (`Nat.toNat` of the port's bignum is `ConRon/Refine/Nat.lean`'s `toNat`),
   and `unescape_from` against `unescapeGo`, both plain index inductions;
3. the references: `name_ref`/`level_ref`/`pw_ref`/`expr_ref` against
   `nameRef`/… under "the tables abstract to the reader's arrays", the
   invariant of the whole pass;
4. the records: eleven `E` arms, three `N`, five `L`, two `W`, one `S`, each a
   forward-reasoning step through the smart constructors already refined in
   `ConRon/Refine/{Name,Level,PropWhen,Expr}.lean`;
5. the pass: induction on the record index with (3)'s invariant.

Task #43 did not attempt it: the statement it would feed —
`pins_text_decodes` — is the one the same task measured to be unreachable, so
the value of the bulk is deferred until that is resolved (see there). -/
theorem pins_decode_refines (t : Str) (v : alloc.vec.Vec nat_op_pins.NatOpPinSet)
    (h : pins_decode.decode t = ok (.Ok v)) :
    ConRon.Dump.parsePins (absText t) = .ok (absPins v) := by
  sorry

/-! ## The closed computation, and why it is open

This is the statement task #43 set out to prove and could not, and the reasons
are the task's deliverable.  Each was measured; none is a matter of patience.

**(a) The Aeneas string model already spends a native-decide axiom.**  Aeneas
renders a `&str` constant as `toStr "…"`, and `toStr`'s bound
`s.toByteArray.size ≤ U32.max` is discharged by its own default argument
`by decide +native` (`Aeneas/Std/String.lean`, with the library's own TODO
saying it should not be).  So, *before any proof of ours*,

    #print axioms ConRon.Generated.kernel.pins_text.PINS_TEXT
    -- [propext, Classical.choice, Quot.sound,
    --  ConRon.Generated.kernel.pins_text.PINS_TEXT._native.decide.ax_1]

`decode` itself is clean (`[propext, Classical.choice, Quot.sound]`).  A
`native_decide`-free theorem *about the constant* is therefore impossible
without an upstream change to Aeneas; the fix is Aeneas's to make (a `Str`
model that carries the `String`, or a `toStr` whose bound is not a side
condition), and until then this is the cost of any embedded text.

**(b) The reference decoder does not reduce in the kernel at all.**
`ConRon.Dump.parsePins` was `partial def` (nothing can be proved about a
`partial def`, and nothing reduces); task #43 made `runLines` total with
`termination_by`, which buys the *statements* above but not evaluation: a
well-founded recursion does not whnf.  Measured on the smallest possible pin
text, 23 bytes:

    example : (parsePins "con-ron-pins/1\nend 0\n").isOk = true := by rfl
    -- Tactic `rfl` failed … is not definitionally equal to `true`   (1.3 s)

`decide` is not available either — `Except String (List NatOpPinSet)` has no
`DecidableEq`, and `Expr`'s would be the structural walk, which is 5.1 M nodes
per variant (task #22).

**(c) Kernel reduction of a string literal is quadratic, so the size alone is
already hopeless.**  The cheapest conceivable claim about the embedded text is
its byte size, and it is `decide`-able (`String.toByteArray` is a projection in
4.33, and a literal does expand).  Measured, on prefixes of the real text, with
`maxHeartbeats 0`:

| prefix | `("…").toByteArray.size ≤ 4294967295` by `decide` |
|---|---|
| 256 B | 3.0 s |
| 1 KB | **27 s** |
| 8 KB | > 300 s (timeout) |
| 532 KB (the text) | ≈ 10⁶–10⁷ s by the quadratic fit |

The quadratic is the literal's expansion into `List.utf8Encode` of its
character list, whose `ByteArray.push` fold is O(n) per byte in the kernel.

**What this rules out, therefore:** the direct route (evaluate the decoder on
the text) by (b) and (c); the round-trip route (prove `parsePins (dumpPins v) =
.ok v` generically, then `PINS_TEXT = dumpPins ConLeche.natOpPinSets` by
`rfl`/`decide`) by (c) — that `rfl` is a 532 KB string equality, and the writer
it must evaluate additionally goes through `Std.HashMap` (UInt64 hashing) and
`String.append`, which is itself quadratic in the kernel; and `native_decide`
by fiat.  The *round-trip theorem* stays worth having — it is the reusable half
and says the format is injective — but it cannot be cashed in on this value in
this kernel.

**What would make it reachable**, in increasing order of upstream cost: a
`Str`/`toStr` model in Aeneas that needs no side condition (removes (a)); a
reference decoder written for kernel evaluation — structural recursion over a
`List UInt8` with `Nat`-keyed `Std.TreeMap` tables instead of `Array`s, which
turns the pass into ≈10⁷ accelerated `Nat` steps — plus a kernel that expands a
string literal linearly (removes (b) and (c)).  Failing all that, the honest
statement is the one the port already has: the embedded text is checked against
con-leche's own `natOpPinSets` by `scripts/gen-pins.sh --check` at build time
and against the writer's bytes by `cargo test`, and the *theorem* speaks about
`decode PINS_TEXT` without saying what it equals. -/
theorem pins_text_decodes :
    ConRon.Dump.parsePins (absText pins_text.PINS_TEXT)
      = .ok ConLeche.natOpPinSets := by
  sorry

/-- **The corollary's shape** (DESIGN.md §1's statement, with the pins closed).
Once `pins_decode_refines` and `pins_text_decodes` hold, the pin list the
binary uses is con-leche's own with no hypothesis: the driver passes
`decode_embedded()`, and that decodes to `natOpPinSets`.  `sorry` here is *not*
only the two above — `cached::installed::check_decls` is not refined yet
(DESIGN.md §5, P3.6), so this is the composition written down in advance, to
show where the pins enter. -/
theorem check_decls_pins_refines
    (v : alloc.vec.Vec nat_op_pins.NatOpPinSet)
    (h : pins_decode.decode_embedded = ok (.Ok v)) :
    absPins v = ConLeche.natOpPinSets := by
  sorry

end ConRon.Refine
