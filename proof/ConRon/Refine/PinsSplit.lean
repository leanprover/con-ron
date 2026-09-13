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

/-- A non-empty list takes at least one byte.  This is what makes the scan
land where it should: an index never stops *inside* a character. -/
theorem ulen_pos {l : List Char} (h : l ≠ []) : 0 < ulen l := by
  cases l with
  | nil => simp at h
  | cons c l => exact Nat.lt_of_lt_of_le (Char.utf8Size_pos c) (Nat.le_add_right _ _)

/-- Advancing a raw position past a character adds its UTF-8 size. -/
theorem pos_add_char {n : Nat} {d : Char} :
    ((⟨n⟩ : String.Pos.Raw) + d) = ⟨n + d.utf8Size⟩ := by
  simp [String.Pos.Raw.ext_iff]

/-- The zero position as an explicit byte index. -/
theorem pos_zero : (0 : String.Pos.Raw) = ⟨0⟩ := rfl

/-- A string's byte size is the UTF-8 length of its characters. -/
theorem utf8ByteSize_eq {s : String} : s.utf8ByteSize = ulen s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  generalize s.toList = l
  induction l with
  | nil => simp
  | cons c l ih => rw [String.ofList_cons]; simp [ih]

/-! ## Reading one character

`String.Pos.Raw.get` is `utf8GetAux` on the character list, which walks the
list adding sizes until it reaches the requested offset. -/

/-- `utf8GetAux` started at offset `n` and asked for offset `n + ulen a`
returns the character that follows `a`. -/
theorem utf8GetAux_append_cons {c : Char} {b : List Char} :
    ∀ (a : List Char) (n : Nat),
      String.Pos.Raw.utf8GetAux (a ++ c :: b) ⟨n⟩ ⟨n + ulen a⟩ = c := by
  intro a
  induction a with
  | nil => intro n; simp [String.Pos.Raw.utf8GetAux]
  | cons d a ih =>
    intro n
    have hpos := Char.utf8Size_pos d
    show String.Pos.Raw.utf8GetAux (d :: (a ++ c :: b)) ⟨n⟩ ⟨n + (d.utf8Size + ulen a)⟩ = c
    rw [String.Pos.Raw.utf8GetAux,
      if_neg (by simp [String.Pos.Raw.ext_iff]; omega)]
    rw [pos_add_char, show n + (d.utf8Size + ulen a) = (n + d.utf8Size) + ulen a from by omega]
    exact ih _

/-- **The character at the offset of a prefix.**  If `s` reads as `a ++ x :: b`
then byte `ulen a` of `s` is `x`. -/
theorem get_eq {s : String} {a b : List Char} {x : Char} (h : s.toList = a ++ x :: b) :
    String.Pos.Raw.get s ⟨ulen a⟩ = x := by
  rw [String.Pos.Raw.get, h, pos_zero, show ulen a = 0 + ulen a from by simp]
  exact utf8GetAux_append_cons a 0

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

/-- **Extracting the middle chunk.**  If `s` reads as `p ++ q ++ r` then the
substring between the byte offsets of `p` and of `p ++ q` is `q`. -/
theorem extract_eq {s : String} {p q r : List Char} (h : s.toList = p ++ q ++ r) :
    String.Pos.Raw.extract s ⟨ulen p⟩ ⟨ulen p + ulen q⟩ = String.ofList q := by
  rw [String.Pos.Raw.extract]
  split
  · rename_i hle
    have hq : q = [] := by
      by_contra hq
      have := ulen_pos hq
      simp at hle
      omega
    subst hq; simp
  · rw [h]
    congr 1
    rw [List.append_assoc, pos_zero,
      show (⟨ulen p⟩ : String.Pos.Raw) = ⟨0 + ulen p⟩ from by simp,
      extract_go₁ p 0, Nat.zero_add, extract_go₂ q (ulen p)]

/-! ## The scan -/

/-- **The invariant of `splitOnAux` at a one-character separator.**  With
`s.toList = p ++ q ++ r` — `p` already emitted, `q` the chunk accumulated
between `b = ulen p` and `i = ulen p + ulen q`, `r` still to read — the scan
emits `acc` reversed followed by the split of `r` with `q` glued onto its first
element.  That last is exactly core's `List.splitOnPPrepend`, whose accumulator
is held reversed, hence `q.reverse`.

The separator being one character wide is what keeps `j` at `0`: the moment a
character matches, `j` reaches the end of the separator, so the "partial match"
branch of the recursion is never taken. -/
theorem splitOnAux_eq (c : Char) (s : String) :
    ∀ (r p q : List Char) (acc : List String), s.toList = p ++ q ++ r →
      String.splitOnAux s (String.singleton c) ⟨ulen p⟩ ⟨ulen p + ulen q⟩ 0 acc
        = acc.reverse ++ (List.splitOnPPrepend (· == c) r q.reverse).map String.ofList := by
  intro r
  induction r with
  | nil =>
    intro p q acc h
    rw [String.splitOnAux.eq_def]
    rw [if_pos (show String.Pos.Raw.atEnd s ⟨ulen p + ulen q⟩ = true by
      simp [String.Pos.Raw.atEnd, utf8ByteSize_eq, h])]
    simp only [extract_eq h]
    simp
  | cons x r ih =>
    intro p q acc h
    have hpx := Char.utf8Size_pos x
    have hget : String.Pos.Raw.get s ⟨ulen p + ulen q⟩ = x := by
      rw [show ulen p + ulen q = ulen (p ++ q) from by simp]
      exact get_eq h
    have hsepget : String.Pos.Raw.get (String.singleton c) 0 = c := by
      rw [String.Pos.Raw.get, String.toList_singleton]
      simp [String.Pos.Raw.utf8GetAux]
    have hnext : String.Pos.Raw.next s ⟨ulen p + ulen q⟩
        = ⟨ulen p + ulen q + x.utf8Size⟩ := by
      rw [String.Pos.Raw.next, hget, pos_add_char]
    have hsepnext : String.Pos.Raw.next (String.singleton c) 0 = ⟨c.utf8Size⟩ := by
      rw [String.Pos.Raw.next, hsepget, pos_zero, pos_add_char, Nat.zero_add]
    have hsepatend : String.Pos.Raw.atEnd (String.singleton c) ⟨c.utf8Size⟩ = true := by
      simp [String.Pos.Raw.atEnd]
    have hnotend : String.Pos.Raw.atEnd s ⟨ulen p + ulen q⟩ = false := by
      simp [String.Pos.Raw.atEnd, utf8ByteSize_eq, h]
      omega
    rw [String.splitOnAux.eq_def]
    simp only [hnotend, hget, hsepget, hnext, hsepnext, hsepatend, Bool.false_eq_true, if_false,
      reduceIte]
    by_cases hxc : x = c
    · -- a separator: `q` is emitted and the scan restarts just after it
      rw [if_pos (show (x == c) = true from by simp [hxc])]
      rw [show (⟨ulen p + ulen q + x.utf8Size⟩ : String.Pos.Raw).unoffsetBy ⟨c.utf8Size⟩
            = ⟨ulen p + ulen q⟩ from by simp [String.Pos.Raw.ext_iff, hxc],
        extract_eq h]
      have IH := ih (p ++ q ++ [x]) [] (String.ofList q :: acc) (by rw [h]; simp)
      simp only [ulen_append, ulen_cons, ulen_nil, Nat.add_zero, List.reverse_nil] at IH
      rw [IH, List.splitOnPPrepend_cons_pos (p := (· == c)) (by simp [hxc])]
      simp
    · -- an ordinary character: it joins the chunk
      rw [if_neg (show ¬ (x == c) = true from by simp [hxc])]
      rw [show (⟨ulen p + ulen q⟩ : String.Pos.Raw).unoffsetBy 0 = ⟨ulen p + ulen q⟩ from by
            simp, hnext]
      have IH := ih p (q ++ [x]) acc (by rw [h]; simp)
      simp only [ulen_append, ulen_cons, ulen_nil, Nat.add_zero, ← Nat.add_assoc] at IH
      rw [IH, List.splitOnPPrepend_cons_neg (p := (· == c)) (by simp [hxc])]
      simp

/-! ## `String.splitOn` at one character -/

/-- **The bridge.**  Splitting a string at a one-character separator is
splitting its character list at that character.  Everything else in this file,
and everything `Refine/PinsRead.lean` needs, is one `List.splitOn` lemma away
from here. -/
theorem splitOn_singleton (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList := by
  rw [String.splitOn, if_neg (show ¬ (String.singleton c == "") = true from by simp)]
  exact splitOnAux_eq c s s.toList [] [] [] rfl

/-- The newline literal `parsePins` splits lines on is a `String.singleton`. -/
theorem newline_eq : "\n" = String.singleton '\n' := by decide

/-- The space literal `parsePins` splits fields on is a `String.singleton`. -/
theorem space_eq : " " = String.singleton ' ' := by decide

/-- A chunk with no separator in it is one token. -/
theorem splitOn_of_not_mem {c : Char} {a : List Char} (ha : c ∉ a) :
    (String.ofList a).splitOn (String.singleton c) = [String.ofList a] := by
  rw [splitOn_singleton, String.toList_ofList, List.splitOn_eq_singleton ha]
  simp

/-- A chunk, the separator, and a rest: the chunk, then the rest's own split. -/
theorem splitOn_append_cons {c : Char} {a b : List Char} (ha : c ∉ a) :
    (String.ofList (a ++ c :: b)).splitOn (String.singleton c)
      = String.ofList a :: (String.ofList b).splitOn (String.singleton c) := by
  rw [splitOn_singleton, splitOn_singleton, String.toList_ofList, String.toList_ofList,
    List.splitOn_append_cons_self_of_not_mem ha]
  simp

/-! ## `absText` on an ASCII text -/

/-- A byte below `128` is its own code point. -/
theorem toNat_ofNat {n : Nat} (h : n < 128) : (Char.ofNat n).toNat = n := by
  rw [Char.ofNat, dif_pos (show n.isValidChar from Or.inl (by omega))]
  simp [Char.toNat, Char.ofNatAux]

/-- UTF-8 is the identity on a byte below `128`: one byte, itself. -/
theorem encode_ascii {n : Nat} (h : n < 128) :
    String.utf8EncodeChar (Char.ofNat n) = [UInt8.ofNat n] := by
  have hv : (Char.ofNat n).val.toNat = n := by simpa using toNat_ofNat h
  rw [String.utf8EncodeChar]
  simp only [hv]
  rw [if_pos (by omega)]

/-- …and so on a whole list of them, one byte per character. -/
theorem flatMap_ascii : ∀ (l : List Nat), (∀ n ∈ l, n < 128) →
    (l.map Char.ofNat).flatMap String.utf8EncodeChar = l.map (fun n => UInt8.ofNat n) := by
  intro l
  induction l with
  | nil => simp
  | cons n l ih =>
    intro h
    simp only [List.map_cons, List.flatMap_cons, encode_ascii (h n (by simp)),
      ih (fun m hm => h m (by simp [hm])), List.singleton_append]

/-- **An ASCII byte string abstracts character for character.**  `absText` is
`String.fromUTF8?`, and UTF-8 is the identity on bytes below `128`. -/
theorem absText_of_ascii {t : Slice Std.U8} (h : ∀ b ∈ bytesOf t, b < 128) :
    absText t = String.ofList ((bytesOf t).map Char.ofNat) := by
  have hb : (String.ofList ((bytesOf t).map Char.ofNat)).toByteArray
      = ⟨(t.val.map (fun b => UInt8.ofNat b.val)).toArray⟩ := by
    rw [String.toByteArray_ofList, List.utf8Encode, flatMap_ascii _ h]
    ext1
    rw [List.data_toByteArray]
    simp [bytesOf]
  unfold absText
  rw [← hb, String.fromUTF8?_toByteArray]

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The `splitOn` bridge is core-only reasoning and the `absText` one is UTF-8
plumbing; neither spends anything beyond con-leche's own three. -/

/-- info: 'ConRon.Refine.PinsSplit.splitOn_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms splitOn_singleton

/-- info: 'ConRon.Refine.PinsSplit.absText_of_ascii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms absText_of_ascii

end ConRon.Refine.PinsSplit
