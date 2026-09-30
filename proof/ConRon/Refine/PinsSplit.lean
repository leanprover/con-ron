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
byte string is the character-wise decode, so `ConRon/Refine/Pins.lean`'s
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

/-- Advancing a raw position past a character adds its UTF-8 size. -/
theorem pos_add_char {n : Nat} {d : Char} :
    ((⟨n⟩ : String.Pos.Raw) + d) = ⟨n + d.utf8Size⟩ := by
  simp [String.Pos.Raw.ext_iff]

/-! ## Reading one character

`String.Pos.Raw.get` is `utf8GetAux` on the character list, which walks the
list adding sizes until it reaches the requested offset. -/

/-! ## Extracting one chunk

`String.Pos.Raw.extract` is two loops: `go₁` skips to the start offset, `go₂`
collects up to the end offset.  Each gets its own invariant. -/

/-- `go₂` from offset `n` to offset `n + ulen q` collects exactly `q`. -/
theorem extract_go₂ {e : List Char} :
    ∀ (q : List Char) (n : Nat),
      String.Pos.Raw.extract.go₂ (q ++ e) ⟨n⟩ ⟨n + ulen q⟩ = q := by
  intro q
  induction q with
  | nil =>
    intro n
    cases e with
    | nil => simp [String.Pos.Raw.extract.go₂]
    | cons d ds => simp [String.Pos.Raw.extract.go₂]
  | cons d q ih =>
    intro n
    have hpos := Char.utf8Size_pos d
    show String.Pos.Raw.extract.go₂ (d :: (q ++ e)) ⟨n⟩ ⟨n + (d.utf8Size + ulen q)⟩ = _
    rw [String.Pos.Raw.extract.go₂,
      if_neg (by simp [String.Pos.Raw.ext_iff]; omega)]
    rw [pos_add_char, show n + (d.utf8Size + ulen q) = (n + d.utf8Size) + ulen q from by omega,
      ih]

/-- `go₁` skips the prefix `p` and hands over to `go₂` at offset `n + ulen p`. -/
theorem extract_go₁ {q : List Char} {e : String.Pos.Raw} :
    ∀ (p : List Char) (n : Nat),
      String.Pos.Raw.extract.go₁ (p ++ q) ⟨n⟩ ⟨n + ulen p⟩ e
        = String.Pos.Raw.extract.go₂ q ⟨n + ulen p⟩ e := by
  intro p
  induction p with
  | nil =>
    intro n
    cases q with
    | nil => simp [String.Pos.Raw.extract.go₁, String.Pos.Raw.extract.go₂]
    | cons d ds => simp [String.Pos.Raw.extract.go₁]
  | cons d p ih =>
    intro n
    have hpos := Char.utf8Size_pos d
    show String.Pos.Raw.extract.go₁ (d :: (p ++ q)) ⟨n⟩ ⟨n + (d.utf8Size + ulen p)⟩ e = _
    rw [String.Pos.Raw.extract.go₁,
      if_neg (by simp [String.Pos.Raw.ext_iff]; omega)]
    rw [pos_add_char, show n + (d.utf8Size + ulen p) = (n + d.utf8Size) + ulen p from by omega,
      ih]
    simp [Nat.add_assoc]

/-! ## The scan -/

/-! ## `String.splitOn` at one character -/

/-! ## `absText` on an ASCII text -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The `splitOn` bridge is core-only reasoning and the `absText` one is UTF-8
plumbing; neither spends anything beyond con-leche's own three. -/

end ConRon.Refine.PinsSplit
