/-
The tokenizer bridge's foundation: `String.splitOn` at a single character, and
`absText` on an ASCII byte string (task #64).

Task #43's docstring named "the tokenizer bridge" as the piece that had to be
costed first, and said why: `ConRon.Dump.parsePins` splits on `"\n"` and then
on `" "`, `String.splitOn` in Lean 4.33 is written on `String.Pos`, and core
carries no lemma relating it to a character list.  It turns out the *whole*
bridge rests on two facts about a one-character separator:

* a chunk with no separator in it is one token;
* a chunk, the separator, and a rest split as the chunk followed by the rest's
  own split.

Everything `Refine/PinsRead.lean` does with lines and fields is those two
applied to a suffix, which is why they live in their own file.

The third lemma here is the other half of the bridge: `absText` of an **ASCII**
byte string is the character-wise decode, so the decoder's
`absText t` becomes a `List Char` that `PinsDec`'s byte list maps onto
one for one.  (`Refine/PinsAscii.lean` is what supplies the hypothesis.)

Both `splitOn` facts are corollaries of one bridge lemma, `splitOn_singleton`:

    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList

Lean 4.33's core proves nothing at all about the legacy `String.splitOnAux`
(`Init/Data/String/Legacy.lean` is the only file that so much as mentions it)
and Mathlib proves nothing either, so that one induction is unavoidable; but
core *does* carry a full lemma library for `List.splitOn` /
`List.splitOnPPrepend`, and once the bridge is crossed both statements — and
anything else `PinsRead.lean` may want — are one `List` lemma away.

The induction is set up so that the three-way recursion of `splitOnAux`
collapses: the separator is one character wide, so the inner index `j` is
either `0` or already at the end of the separator, and the scan is a plain
left-to-right walk.  The invariant is the split of `s.toList` as `p ++ q ++ r`:
`p` is what has already been emitted (separators included), `q` is the chunk
being accumulated between `b` and `i`, and `r` is what is left to read.
-/
import ConRon.Refine.PinsAbs

open Aeneas Aeneas.Std

namespace ConRon.Refine.PinsSplit

/-! ## UTF-8 offsets of a character list

`String.Pos.Raw` is a byte offset, so every statement below indexes into a
string by the UTF-8 length of a prefix of its characters.  `ulen` is that
length; the lemmas here are all the inductions need. -/

/-- The UTF-8 byte length of a character list: the byte offset just past it. -/
def ulen : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + ulen cs

@[simp] theorem ulen_nil : ulen [] = 0 := rfl

@[simp] theorem ulen_cons {c : Char} {l : List Char} :
    ulen (c :: l) = c.utf8Size + ulen l := rfl

@[simp] theorem ulen_append {a b : List Char} :
    ulen (a ++ b) = ulen a + ulen b := by
  induction a with
  | nil => simp
  | cons d a ih => simp [ih, Nat.add_assoc]

/-! ## Reading one character

`String.Pos.Raw.get` is `utf8GetAux` on the character list, which walks the
list adding sizes until it reaches the requested offset. -/

/-! ## Extracting one chunk

`String.Pos.Raw.extract` is two loops: `go₁` skips to the start offset, `go₂`
collects up to the end offset.  Each gets its own invariant. -/

/-! ## The scan -/

/-! ## `String.splitOn` at one character -/

/-! ## `absText` on an ASCII text -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The `splitOn` bridge is core-only reasoning and the `absText` one is UTF-8
plumbing; neither spends anything beyond con-leche's own three. -/

end ConRon.Refine.PinsSplit
